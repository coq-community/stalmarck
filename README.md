# Stalmarck

[![CI][action-shield]][action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[action-shield]: https://github.com/coq-community/stalmarck/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/coq-community/stalmarck/actions?query=workflow%3ACI

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/3-540-44659-1_24.svg
[doi-link]: https://doi.org/10.1007/3-540-44659-1_24

A two-level approach to prove tautologies using Stålmarck's algorithm in Coq.


## Meta

- Author(s):
  - Pierre Letouzey (initial)
  - Laurent Théry (initial)
- Coq-community maintainer(s):
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: Coq master (use the corresponding branch or release for other Coq versions)
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

