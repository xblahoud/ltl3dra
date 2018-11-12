/***** ltl3dra : optim.c *****/

/* Written by Tomas Babiak, FI MU, Brno, Czech Republic                   */
/* Copyright (c) 2012  Tomas Babiak                                       */
/*                                                                        */

#include "ltl3dra.h"

#define false 0
#define true 1

int is_negatedPredicate(Node *n) {
  if (!n) return false;

  if (n->ntyp == NOT && n->lft && n->lft->ntyp == PREDICATE) return true;
  return false;
}

int is_G(Node *n) {
  if (!n) return false;

  if (n->ntyp == V_OPER && n->lft && n->lft->ntyp == FALSE) return true;
  else return false;
}

int is_F(Node *n) {
  if (!n) return false;

  if (n->ntyp == U_OPER && n->lft && n->lft->ntyp == TRUE) return true;
  else return false;
}

int is_Falpha(Node *n) {
  if (!n) return false;

  if (is_F(n) && is_LTL(n->rgt))
    return true;
  else
    return false;
}

int is_Gconj(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {

  case AND:
    return is_Gconj(n->lft) && is_Gconj(n->rgt);
    break;
  case V_OPER:

    if (is_G(n))
      return true;
    else
      return false;
    break;
  case OR:
  case U_OPER:
#ifdef NXT
  case NEXT:
#endif
  case NOT:
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_Gdisj(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {

  case OR:
    return is_Gdisj(n->lft) && is_Gdisj(n->rgt);
    break;
  case V_OPER:

    if (is_G(n))
      return true;
    else
      return false;
    break;
  case AND:
  case U_OPER:
#ifdef NXT
  case NEXT:
#endif
  case NOT:
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_Fconj(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {

  case AND:
    return is_Fconj(n->lft) && is_Fconj(n->rgt);
    break;
  case U_OPER:

    if (is_F(n))
      return true;
    else
      return false;
    break;
  case OR:
  case V_OPER:
#ifdef NXT
  case NEXT:
#endif
  case NOT:
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_Fdisj(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {

  case OR:
    return is_Fdisj(n->lft) && is_Fdisj(n->rgt);
    break;
  case U_OPER:

    if (is_F(n))
      return true;
    else
      return false;
    break;
  case AND:
  case V_OPER:
#ifdef NXT
  case NEXT:
#endif
  case NOT:
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_UXp(Node *n) {
  if (!n) return false;

  if (n->ntyp == U_OPER
#ifdef NXT
      || n->ntyp == NEXT
#endif
      || is_LTL(n)) return true;
  else return false;
}

/* Checks whether the given formula is in the LTL(F_s, G_s) fragment
 * of the ATVA'13 paper, i.e.,
 * limited to the temporal operators F, G and XF, XG.
 */
int is_LTL_Fs_Gs(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {
  case OR:
  case AND:
    return is_LTL_Fs_Gs(n->lft) && is_LTL_Fs_Gs(n->rgt);
    break;
  case U_OPER:
    return is_F(n) && is_LTL_Fs_Gs(n->rgt);
  case V_OPER:
    return is_G(n) && is_LTL_Fs_Gs(n->rgt);
#ifdef NXT
  case NEXT:
    return (is_F(n->lft) || is_G(n->lft))
      && is_LTL_Fs_Gs(n->lft);
#endif
  case NOT: // formula not in PNF...
    if (is_negatedPredicate(n)) return true;
    printf("Internal error: formula not in PNF");
    exit(1);
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return true;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
  }
}

/* Checks whether the given formula is in in the fragment
 * of LTL defined in Sec. 8 of the ATVA'13 paper, i.e.,
 *   phi = psi | phi or phi | phi and phi | X phi | phi U phi
 * where psi is a formula in LTL(F_s, G_s)
 */
int is_limLTL(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {
  case OR:
  case AND:
    return is_limLTL(n->lft) && is_limLTL(n->rgt);
    break;
  case U_OPER:
    return is_limLTL(n->lft) && is_limLTL(n->rgt);
  case V_OPER:
    return is_LTL_Fs_Gs(n);
#ifdef NXT
  case NEXT:
    return is_limLTL(n->lft);
#endif
  case NOT: // formula not in PNF...
    if (is_negatedPredicate(n)) return true;
    printf("Internal error: formula not in PNF");
    exit(1);
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return true;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
  }
}

// Checks whether it is a fromula of LTL() fragment (boolean combination of APs)
int is_LTL(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {
  case OR:
  case AND:
    return is_LTL(n->lft) && is_LTL(n->rgt);
    break;
  case U_OPER:
  case V_OPER:
    return false;
    break;
#ifdef NXT
  case NEXT:
    return false;
    break;
#endif
  case NOT:
    return is_LTL(n->lft);
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return true;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_EVE(Node *n) {
  if (!n) return false;

  if (is_F(n)) return true;

  switch(n->ntyp) {
  case OR:
  case AND:
    return is_EVE(n->lft) && is_EVE(n->rgt);
    break;
  case U_OPER:
    return is_EVE(n->rgt);
    break;
  case V_OPER:
    if (is_G(n))
      return is_EVE(n->rgt);
    else
      return is_EVE(n->lft) && is_EVE(n->rgt);
    break;
#ifdef NXT
  case NEXT:
    return is_EVE(n->lft);
    break;
#endif
  case NOT:
    return is_EVE(n->lft); /* negacia by mala byt iba pred predikatmi (???) */
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_UNI(Node *n) {
  if (!n) return false;

  if (is_G(n)) return true;

  switch(n->ntyp) {
  case OR:
  case AND:
    return is_UNI(n->lft) && is_UNI(n->rgt);
    break;
  case U_OPER:
    if (is_F(n))
      return is_UNI(n->rgt);
    else
      return is_UNI(n->lft) && is_UNI(n->rgt);
    break;
  case V_OPER:
    return is_UNI(n->rgt);
    break;
#ifdef NXT
  case NEXT:
    return is_UNI(n->lft);
    break;
#endif
  case NOT:
    return is_UNI(n->lft); /* negacia by mala byt iba pred predikatmi (???) */
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_FIN(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {
  case OR:
  case AND:
    return is_FIN(n->lft) && is_FIN(n->rgt);
    break;
  case U_OPER:
    return is_FIN(n->lft) && is_FIN(n->rgt);
    break;
  case V_OPER:
    return false;
    break;
#ifdef NXT
  case NEXT:
    return is_FIN(n->lft);
    break;
#endif
  case NOT:
    return is_FIN(n->lft); /* negacia by mala byt iba pred predikatmi (???) */
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return true;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_INFp(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {
  case OR:
  case AND:
    return is_INFp(n->lft) && is_INFp(n->rgt);
    break;
  case U_OPER:
    if (is_F(n))
      return is_UNI(n->rgt);
    else
      return is_INFp(n->rgt);
    break;
  case V_OPER:
    if (is_G(n))
      return is_EVE(n->rgt);
    else
      return is_INFp(n->rgt);
    break;
#ifdef NXT
  case NEXT:
    return is_INFp(n->lft);
    break;
#endif
  case NOT:
    return is_INFp(n->lft); /* negacia by mala byt iba pred predikatmi (???) */
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_INFd(Node *n) {
  if (!n) return false;

  if (is_INFp(n)) return true;

  switch(n->ntyp) {
  case OR:
    return false;
    break;
  case AND:
    return is_INFd(n->lft) && is_INFd(n->rgt);
    break;
  case U_OPER:
    return false;
    break;
  case V_OPER:
    if (is_G(n)) {
      if (is_LTL(n->rgt))
        return true;
      else
        return is_INFd(n->rgt);
    } else
        return false;
    break;
#ifdef NXT
  case NEXT:
    return false;
    break;
#endif
  case NOT:
    return is_INFd(n->lft); /* negacia by mala byt iba pred predikatmi (???) */
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_GF_inside(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {
  case OR:
    return is_LTL(n->lft) && is_LTL(n->rgt);
    break;
  case AND:
    return is_GF_inside(n->lft) && is_GF_inside(n->rgt);
    break;
  case U_OPER:
    if (is_F(n) && is_LTL(n->rgt))
      return true;
    else return false;
    break;
  case V_OPER:
    return false;
    break;
#ifdef NXT
  case NEXT:
    return false;
    break;
#endif
  case NOT:
    return is_GF_inside(n->lft); /* negacia by mala byt iba pred predikatmi (???) */
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return true;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}

int is_GF_component(Node *n) {
  if (!n) return false;

  if (!is_G(n)) return false;

  if (is_GF_inside(n->rgt)) return true;
  else return false;
}

int has_X(Node *n) {
  if (!n) return false;

  switch(n->ntyp) {
  case OR:
  case AND:
  case U_OPER:
  case V_OPER:
    return has_X(n->lft) || has_X(n->rgt);
    break;
#ifdef NXT
  case NEXT:
    return true;
    break;
#endif
  case NOT:
    return has_X(n->lft);
    break;
  case FALSE:
  case TRUE:
  case PREDICATE:
    return false;
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    exit(1);
    break;
  }
}
