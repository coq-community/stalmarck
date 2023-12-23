<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Stalmarck

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/stalmarck/actions/workflows/docker-action.yml/badge.svg?branch=v8.19
[docker-action-link]: https://github.com/coq-community/stalmarck/actions/workflows/docker-action.yml

[nix-action-shield]: https://github.com/coq-community/stalmarck/actions/workflows/nix-action.yml/badge.svg?branch=v8.19
[nix-action-link]: https://github.com/coq-community/stalmarck/actions/workflows/nix-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/3-540-44659-1_24.svg
[doi-link]: https://doi.org/10.1007/3-540-44659-1_24

A two-level approach to prove tautologies using Stålmarck's
algorithm in Coq.

## Meta

- Author(s):
  - Pierre Letouzey (initial)
  - Laurent Théry (initial)
- Coq-community maintainer(s):
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: 8.19 (use the corresponding branch or release for other Coq versions)
- Additional dependencies: none
- Coq namespace: `Stalmarck.Algorithm`
- Related publication(s):
  - [Formalizing Stålmarck's Algorithm in Coq](https://www.irif.fr/~letouzey/download/stalmarck.ps.gz) doi:[10.1007/3-540-44659-1_24](https://doi.org/10.1007/3-540-44659-1_24)

## Building and installation instructions

The easiest way to install the latest released version of Stalmarck
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stalmarck
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/stalmarck.git
cd stalmarck
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

This project is composed of:

- A Coq proof of correctness of the algorithm, as described in the paper
  [A Formalization of Stålmarck's Algorithm in Coq][paper-link], published
  in the proceedings of TPHOLs 2000.
- an implementation of the algorithm. With respect to the paper, this
  implementation is completely functional and can be used inside Coq.
- A reflected Coq tactic `staltac` that uses the extracted code to compute
  an execution trace; the trace checker is then called inside Coq.
- A standalone checker program `stalmarck` which takes as input a formula in
  textual format and reports whether it can be certified as a tautology.

See `algoRun.v` for examples how to use the algorithm inside Coq, and
see `StalTac_ex.v` for examples how to use the reflected tactic.

[paper-link]: https://www.irif.fr/~letouzey/download/stalmarck.ps.gz

## Tautology Checker

The `src` directory contains the code for a standalone tautology checker
using the implementation of Stålmarck's algorithm extracted from Coq.

### Running the checker

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
The other output is `Don't know` (and exit code 1): either the formula
is not a tautology, or it is one but the program cannot conclude this
(insufficient level).

## Example

An example file with a tautology ([`tests/ztwaalf1_be`](tests/ztwaalf1_be))
is included, and can be checked as follows:
```shell
stalmarck 1 tests/ztwaalf1_be
Tautology
```

