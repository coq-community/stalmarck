# Stalmarck Tautology Checker

This directory contains the code for a standalone tautology checker using
the implementation of Stålmarck's algorithm extracted from Coq.

## Running the checker

```shell
stalmarck <level> <file>
```
where: 
- `<level>` is an integer controling depth of dilemma. Usual values:
  - 0: does only propagation.
  - 1: dilemma upon one variable at the same time.
  - 2: dilemma can be done upon two variables at the same time; more than 2 may take *very* long.
- `<file>` is the file containing the boolean formula.

## Boolean formula syntax

| Concept  | Syntax |
| -------- | ------ |
| Comments | `//`  (reading is suspended until the end of the line) |
| Variable | any alphanumeric sequence plus the character `_` |
| Not      | `~` |
| And      | `&` |
| Or       | `#` |
| Implication |	`->`  |
| Equivalence |	`<->` |
| Parentheses |	`( )` |
| True value  | `<T>` |
| False value |	`<F>` |

Priority of connectives, from lower to higher:
- `<->`, `->` (associate to the right)
- `#` (associates to the left)
- `&` (associates to the left)
- `~`

## Output

The only interesting output is `Tautology` (and exit code 0).
The other output is `Don't know` (and exit code 1): either the formula is not
a tautology, or it is one but the program cannot conclude this
(insufficient level).

## Example

One example file with a tautology ([`ztwaalf1_be`](ztwaalf1_be)) is included.
```shell
stalmarck 1 ztwaalf1_be
Tautology
```
