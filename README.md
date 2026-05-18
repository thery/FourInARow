<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# FourInARow

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/fiar/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/fiar/actions/workflows/docker-action.yml




Four-In-a-Row in Rocq


| File                              |  Content                                 | 
| --------------------------------- | -----------------------------------------| 
| [ssr_int](./ssr_int.v)            | native int for mathcomp                  | 
| [FourInARow](./FourInARow.v)      | the evaluator                            | 
| [Pbasic](./Pbasic.v)              | basic definitions and properties         |
| [Pmoves](./Pmoves.v)              | move generator                           |
| [Phash](./Phash.v)                | hash table                               |
| [Palphabeta](./Palphabeta.v)      | alpha beta pruning                       |
| [Pev1](./Pev1.v)                  | first position                           |
| [Pev2](./Pev2.v)                  | second position                          |
| [Pev3](./Pev3.v)                  | third position                           |
| [Pev4](./Pev4.v)                  | fourth position                          |
| [Pmain](./Pmain.v)                | main theorem                             |

A note about this development is available 
[here](https://inria.hal.science/hal-05625464).

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Rocq/Coq versions: 9.1 or later
- Additional dependencies:
  - [MathComp ssreflect 2.5 or later](https://math-comp.github.io)
- Rocq/Coq namespace: `FourInARow`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of FourInARow
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-fiar
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/thery/fiar.git
cd fiar
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



