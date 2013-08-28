/***** ltl3dra : trans.c *****/

/* Written by Denis Oddoux, LIAFA, France                                 */
/* Copyright (c) 2001  Denis Oddoux                                       */
/* Modified by Paul Gastin, LSV, France                                   */
/* Copyright (c) 2007  Paul Gastin                                        */
/* Modified by Tomas Babiak, FI MU, Brno, Czech Republic                  */
/* Copyright (c) 2012  Tomas Babiak                                       */
/* Modified by Tomas Babiak and Frantisek Blahoudek, Brno, Czech Republic */
/* Copyright (c) 2013  Tomas Babiak and Frantisek Blahoudek               */
/*                                                                        */
/* This program is free software; you can redistribute it and/or modify   */
/* it under the terms of the GNU General Public License as published by   */
/* the Free Software Foundation; either version 2 of the License, or      */
/* (at your option) any later version.                                    */
/*                                                                        */
/* This program is distributed in the hope that it will be useful,        */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/* GNU General Public License for more details.                           */
/*                                                                        */
/* You should have received a copy of the GNU General Public License      */
/* along with this program; if not, write to the Free Software            */
/* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA*/
/*                                                                        */
/* Based on the translation algorithm by Gastin and Oddoux,               */
/* presented at the 13th International Conference on Computer Aided       */
/* Verification, CAV 2001, Paris, France.                                 */
/* Proceedings - LNCS 2102, pp. 53-65                                     */
/*                                                                        */
/* and on paper by                                                        */
/* T. Babiak, M. Kretinsky, V. Rehak, and J. Strejcek,                    */
/* LTL to Buchi Automata Translation: Fast and More Deterministic         */
/* presented at the 18th International Conference on Tools and            */
/* Algorithms for the Construction and Analysis of Systems (TACAS 2012)   */
/*                                                                        */
/* The translation to deterministic Rabin automata is based on paper by   */
/* T. Babiak, F. Blahoudek, M. Kretinsky, and J. Strejcek                 */
/* Effective Translation of LTL to Deterministic Rabin Automata:          */
/* Beyond the (F,G)-Fragment (2013)                                       */
/* In 11th International Symposium on Automated Technology for            */
/* Verification and Analysis (ATVA 2013)                                  */

#include "ltl3dra.h"
#include <bdd.h>

extern int tl_verbose, tl_terse, tl_errs, tl_tgba_out, tl_dra_out;
extern FILE	*tl_out;

int	Stack_mx=0, Max_Red=0, Total=0;
static char	dumpbuf[2048];

#ifdef NXT
int
only_nxt(Node *n)
{
        switch (n->ntyp) {
        case NEXT:
                return 1;
        case OR:
        case AND:
                return only_nxt(n->rgt) && only_nxt(n->lft);
        default:
                return 0;
        }
}
#endif

int
dump_cond(Node *pp, Node *r, int first)
{       Node *q;
        int frst = first;

        if (!pp) return frst;

        q = dupnode(pp);
        q = rewrite(q);

        if (q->ntyp == PREDICATE
        ||  q->ntyp == NOT
#ifndef NXT
        ||  q->ntyp == OR
#endif
        ||  q->ntyp == FALSE)
        {       if (!frst) fprintf(tl_out, " && ");
                dump(q);
                frst = 0;
#ifdef NXT
        } else if (q->ntyp == OR)
        {       if (!frst) fprintf(tl_out, " && ");
                fprintf(tl_out, "((");
                frst = dump_cond(q->lft, r, 1);

                if (!frst)
                        fprintf(tl_out, ") || (");
                else
                {       if (only_nxt(q->lft))
                        {       fprintf(tl_out, "1))");
                                return 0;
                        }
                }

                frst = dump_cond(q->rgt, r, 1);

                if (frst)
                {       if (only_nxt(q->rgt))
                                fprintf(tl_out, "1");
                        else
                                fprintf(tl_out, "0");
                        frst = 0;
                }

                fprintf(tl_out, "))");
#endif
        } else  if (q->ntyp == V_OPER
                && !anywhere(AND, q->rgt, r))
        {       frst = dump_cond(q->rgt, r, frst);
        } else  if (q->ntyp == AND)
        {
                frst = dump_cond(q->lft, r, frst);
                frst = dump_cond(q->rgt, r, frst);
        }

        return frst;
}

static void
sdump(Node *n)
{
	switch (n->ntyp) {
	case PREDICATE:	strcat(dumpbuf, n->sym->name);
			break;
	case U_OPER:	strcat(dumpbuf, "U");
			goto common2;
	case V_OPER:	strcat(dumpbuf, "V");
			goto common2;
	case OR:	strcat(dumpbuf, "|");
			goto common2;
	case AND:	strcat(dumpbuf, "&");
common2:		sdump(n->rgt);
common1:		sdump(n->lft);
			break;
#ifdef NXT
	case NEXT:	strcat(dumpbuf, "X");
			goto common1;
#endif
	case NOT:	strcat(dumpbuf, "!");
			goto common1;
	case TRUE:	strcat(dumpbuf, "T");
			break;
	case FALSE:	strcat(dumpbuf, "F");
			break;
	default:	strcat(dumpbuf, "?");
			break;
	}
}

Symbol *
DoDump(Node *n)
{
	if (!n) return ZS;

	if (n->ntyp == PREDICATE)
		return n->sym;

	dumpbuf[0] = '\0';
	sdump(n);
	return tl_lookup(dumpbuf);
}

void trans(Node *p) 
{	
  if (!p || tl_errs) return;
  
  if (tl_verbose || tl_terse) {	
    fprintf(tl_out, "\t/* Normlzd: ");
    dump(p);
    fprintf(tl_out, " */\n");
  }
  if (tl_terse)
    return;

/*  dump(p);
  fprintf(tl_out, "\n\n");  */

/*  fprintf(tl_out, "Is EVE?:\n");
  if (is_EVE(p)) fprintf(tl_out, "\tYES!\n\n");
  else fprintf(tl_out, "\tNO!\n\n");

  fprintf(tl_out, "Is UNI?:\n");
  if (is_UNI(p)) fprintf(tl_out, "\tYES!\n\n");
  else fprintf(tl_out, "\tNO!\n\n");

  fprintf(tl_out, "Is FIN?:\n");
  if (is_FIN(p)) fprintf(tl_out, "\tYES!\n\n");
  else fprintf(tl_out, "\tNO!\n\n");

  fprintf(tl_out, "Is INFp?:\n");
  if (is_INFp(p)) fprintf(tl_out, "\tYES!\n\n");
  else fprintf(tl_out, "\tNO!\n\n");

  fprintf(tl_out, "Is INFd?:\n");
  if (is_INFd(p)) fprintf(tl_out, "\tYES!\n\n");
  else fprintf(tl_out, "\tNO!\n\n");*/
  
  // Buddy might have been initialized by a third-party library.
  if (!bdd_isrunning()) {
    bdd_init(100000, 10000);
    //bdd_setvarnum(2);
    // Disable the default GC handler.
    bdd_gbc_hook(0);
  }

  mk_alternating(p);
#ifdef DRA
  if (!tl_dra_out) {
#endif
    mk_generalized();
    if (!tl_tgba_out)
      mk_buchi();
#ifdef DRA
  } else {
    mk_dra();
    mk_ra();
  }
#endif
  
  releasenode(1, p);
  
  bdd_done();
}

