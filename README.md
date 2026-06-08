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
| [FourInARow](./FourInARow.v)      | the generic evaluator                    | 
| [FourInARow47](./FourInARow47.v)  | the evaluator for 4x7                    | 
| [FourInARow56](./FourInARow56.v)  | the evaluator for 5x6                    | 
| [FourInARow57](./FourInARow57.v)  | the evaluator for 5x7                    | 
| [FourInARow65](./FourInARow65.v)  | the evaluator for 6x5                    | 
| [FourInARow66](./FourInARow66.v)  | the evaluator for 6x6                    | 
| [FourInARow67](./FourInARow67.v)  | the evaluator for 6x7                    | 
| [FourInARow74](./FourInARow74.v)  | the evaluator for 7x4                    | 
| [FourInARow75](./FourInARow75.v)  | the evaluator for 7x5                    | 
| [FourInARow76](./FourInARow76.v)  | the evaluator for 7x6                    | 
| [Eval47](./Eval47.v)              | the correctness for for 4x7              | 
| [Eval56](./Eval56.v)              | the correctness for for 5x6              | 
| [Eval57](./Eval57.v)              | the correctness for for 5x7              | 
| [Eval65](./Eval65.v)              | the correctness for for 6x5              | 
| [Eval66](./Eval66.v)              | the correctness for for 6x6              | 
| [Eval67](./Eval67.v)              | the correctness for for 6x7              | 
| [Eval74](./Eval74.v)              | the correctness for for 7x4              | 
| [Eval75](./Eval75.v)              | the correctness for for 7x5              | 
| [Eval76](./Eval76.v)              | the correctness for for 7x6              | 
| [Pbasic](./Pbasic.v)              | basic definitions and properties         |
| [Pmoves](./Pmoves.v)              | move generator                           |
| [Phash](./Phash.v)                | hash table                               |
| [Palphabeta](./Palphabeta.v)      | alpha beta pruning                       |
| [Pev67_1](./Pev67_1.v)            | first position for 6x7 Board             |
| [Pev67_2](./Pev67_2.v)            | second position for 6x7 Board            |
| [Pev67_3](./Pev67_3.v)            | third position for 6x7 Board             |
| [Pev67_4](./Pev67_4.v)            | forth position for 6x7 Board             |
| [Pev67_5](./Pev67_5.v)            | fifth position for 6x7 Board             |
| [Pev67_6](./Pev67_6.v)            | sixth position for 6x7 Board             |
| [Pev76_1](./Pev76_1.v)            | first position for 7x6 Board             |
| [Pev76_2](./Pev76_2.v)            | second position for 7x6 Board            |
| [Pev76_3](./Pev76_3.v)            | third position for 7x6 Board             |
| [Pev76_4](./Pev76_4.v)            | forth position for 7x6 Board             |
| [Pmain67](./Pmain67.v)            | main theorem for 6x7                     |
| [Pmain76](./Pmain76.v)            | main theorem for 7x6                     |
| [Ptable](./Ptable.v)              | the table                                |

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



