version 0.2.1 (2015-02-02):
  -- bug fixes:
    -- -B option produced TGDRA instead of BA-neverclaim
    -- -t dption for statistics did not work
    -- formating issues in HOAF output
  Thanks Alexandre Duret-Lutz for reporting these bugs.

version 0.2 (2015-02-02):
  -- added options for HOAF output
  -- options for output redesigned. Ltl2star has now -L, HOAF -F and the 
       original outputs of ltl3dra v.0.2 -T. One can now specify which automaton
       should be printed:
         1: VWAA
         2: TGDRA
         3: DRA
  -- bug fixes of LTL3BA 1.2 included
  -- utilities tgdra and tgdra3dot added

version 0.1.1 (2013-09-09):
  -- fixed bug in ltl2dstar output format: 
    -- wrong number of states,
    -- wrong numbering of acceptance conditions.
  Thanks Alexandre Duret-Lutz for reporting it.
