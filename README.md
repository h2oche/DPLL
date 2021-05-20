# DPLL
SAT solver using DPLL algorithm with clause learning

```
$ python solvepy3.py PATH_TO_INPUT
```

## Input/Ouput

Input/Output  is always CNF formula in [DIMACS format](https://people.sc.fsu.edu/~jburkardt/data/cnf/cnf.html).

### Input Grammar

- input := lines
- numbers := "" | number " " numbers
- lines := "" | line lines
- line := comment | shape | clause
- comment := "c" string
- shape := "p" "cnf" number number
  - the first number: the # of variables
  - the second number: the # of clauses
- clause := numbers "0"
  - Number should be an element of \[-nbvars, nbvars\].
  - Positive numbers denote the corresponding variables
  - Negative numbers denote the negations of the corresponding variables.
  - Clause can't contain the opposite literal i and -i simultaneously.

Example: `(P_1 \/ !P_5 \/ P_4) /\ (!P_1 \/ P_5 \/ P_3 \/ P_4) /\ (!P_3 \/ !P_4)`
```
c
c start with comments
c
c
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0
```

### Output Grammar

- output := "s" SAT "v" assignments "0"
- SAT := "SATISFIABLE" | "UNSATSIFIABLE"
- assignments := "" | number " " assignments
  - For example `2 5 -7` means that `P_2` and `P_5` has the true value and `P_7` has the false value.

Example:
```
s SATISFIABLE v 2 5 -7 0
```
