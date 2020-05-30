# Stalmarck

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]
[![DOI][doi-shield]][doi-link]

[travis-shield]: https://travis-ci.com/coq-community/stalmarck.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/stalmarck/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby

[doi-shield]: https://zenodo.org/badge/DOI/10.1007/3-540-44659-1_24.svg
[doi-link]: https://doi.org/10.1007/3-540-44659-1_24

A two-level approach to prove tautologies using Stålmarck's algorithm in Coq.


More details about the project can be found in the paper
[Formalizing Stålmarck's Algorithm in Coq](https://www.irif.fr/~letouzey/download/stalmarck.ps.gz).

## Meta

- Author(s):
  - Pierre Letouzey (initial)
  - Laurent Théry (initial)
- Coq-community maintainer(s):
  - Hugo Herbelin ([**@herbelin**](https://github.com/herbelin))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: 8.11 (use the corresponding branch or release for other Coq versions)
- Compatible OCaml versions: all versions supported by Coq
- Additional Coq dependencies: none

## Building and installation instructions

The easiest way to install the latest released version of Stalmarck
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stalmarck
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/stalmarck
cd stalmarck
make   # or make -j <number-of-cores-on-your-machine>
make install
```

After installation, the included modules are available under
the `Stalmarck` namespace.


## Documentation

This project is composed of:

- a proof of correctness of the algorithm as described in 
  "A Formalization of Stålmarck's Algorithm in Coq", TPHOLs2000.

- an implementation of the algorithm. With respect to the paper,
  this implementation is completely functional and can be used inside
  Coq.

- a reflected tactic `staltac`, that uses the extracted code to compute
  an execution trace; the trace checker is then called inside Coq.

See `algoRun.v` for examples how to use the algorithm inside Coq.

See `StalTac_ex.v` for examples how to use the reflected tactic.

WARNING: Stålmarck's method is patented and should not be used for commercial
applications without the agreement of Prover Technology.

