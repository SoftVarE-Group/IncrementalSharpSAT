# IncSharpSAT
IncSharpSAT is an incremental \#SAT solver based on the \#SAT solver [sharpSAT](https://github.com/marcthurley/sharpSAT).

## Building
Run

`./setupdev.sh`

to prepare the build environment, then change to `build/Release` and run

`make`

to build.

Dependencies:

- CMake
- GMP bignum
- gtest

## Usage
`incSharpSAT [filename]`

Solves all queries in the specified file. If no file is given, queries can be provided via stdin.

`incSharpSAT -stdin [filename]`

Solves all queries in the specified file, then takes further queries via stdin. This can be useful to make manual queries after solving a large formula.

Note that by default, clause removal is not permitted. It can be enabled with the option `-r`.

`incSharpSAT -h`

displays further options

### Query format
Every CNF formula in DIMACS is a valid query for this solver. However, the solver adds the specifyied variables and clauses to the already existing formula. For example, the query

```
p cnf 2 1
1 -2 0
```

followed by  the query

```
p cnf 1 1
2 -3 0
```

results in the same formula as

```
p cnf 3 2
1 -2 0
2 -3 0
```

Assumptions can be specified with a single line starting with an `a`, followed by the assumptions as literals and closed by a `0`. This line must be placed directly before the `p cnf` line. For example, the query

```
a -1 2 0
p cnf 0 0
```

applies assumptions which set variable `1` to `FALSE` and variable `2` to `TRUE` to the previous formula.

To remove clauses, the number of removed clauses must first be specified as a third number in the `p cnf` line. Afterwards, each clause removal consists of a line starting with an `r`, followed by the literals in the clause and closed by a `0`. For example, the query

```
p cnf 0 0 1
r 1 -2 0
```

removes the clause `1 -2` from the formula. Note that clause removal is only permitted if the solver was executed with the `-r` option.

These types of query can also be combined. For example,

```
a 5 0
p cnf 2 1 1
r 2 -3 0
4 0
```

is a valid query which adds two variables, adds the clause `4`, removes the clause `2 -3` and sets the variable `5` to `TRUE` via an assumption.
