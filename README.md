# AlgebrasTQD

`AlgebrasTQD` is code written in the [Groups, Algorithms and Programming (GAP) system](https://www.gap-system.org/). 

It provides functions for studying (etale or condensable) algebras in twisted quantum doubles and computes their algebra structure and anyon content, interfaces between topological orders, relations between the associated quantum phases, and quantum computing gates in non-Abelian topological codes.

Package author: [Alison Warman](https://www.maths.ox.ac.uk/people/alison.warman).

The mathematics behind the code is described in [Twin Algebras (Y. Gai, S. Schafer-Nameki, A. Warman)][Gai:2026hjk] drawing on previous work by [A. Davydov and D. Simmons][davydov2017lagrangian] and [A. Gruen and S. Morrison][gruen2021computing].

Other papers with applications of this code can be found on the author's [INSPIRE profile](https://inspirehep.net/authors/2724182).

## Installation

Install [GAP](https://www.gap-system.org/install/) and the `HAP`, `CTblLib`, `IO` packages and `repsn` as some examples use it. 

Download the ZIP archive of this AlgebrasTQD GitHub project and unzip it. 

Start GAP in the `AlgebrasTQD-main` directory which contains `AlgebrasTQD.g` by running:
```
gap
```
then read the AlgebrasTQD package with:
```
Read("AlgebrasTQD.g");
```
This does not install any software but loads the `AlgebrasTQD` source files:

- [`source/0_Modular_Data_Mignard-Schauenburg-Gruen-Morrison.g`](source/0_Modular_Data_Mignard-Schauenburg-Gruen-Morrison.g)
- [`source/1_preliminaries.g`](source/1_preliminaries.g)
- [`source/2_anyons.g`](source/2_anyons.g)
- [`source/3_cocycles.g`](source/3_cocycles.g)
- [`source/4_algebra_data.g`](source/4_algebra_data.g)
- [`source/5_interface_map.g`](source/5_interface_map.g)
- [`source/6_algebra_classes_and_inclusions.g`](source/6_algebra_classes_and_inclusions.g)
- [`source/7_quantum_computing.g`](source/7_quantum_computing.g)

From the GAP prompt in the `AlgebrasTQD-main` directory, all the `AlgebrasTQD` functions can then be executed.

## Examples

The scripts in `examples/` show these calculations in use. They can be read directly, without previously running `gap` or `Read("AlgebrasTQD.g");` .
They include twin algebra and interface examples, as well as quantum computing calculations.

Launch GAP from the `AlgebrasTQD-main` directory (if not already done):

```
gap
```
Then any line below to run the corresponding example file:
``` 
Read("examples/0_load.g");
Read("examples/1_Abelian.g");
Read("examples/2_non-Abelian.g");
Read("examples/3_cocycles.g");
Read("examples/4_algebras.g");
Read("examples/5_interface_map.g");
Read("examples/6_algebra_classes_and_inclusions.g");
Read("examples/7_twin_algebras_G32.g");
Read("examples/8_twin_algebras_GL23.g");
Read("examples/9_quantum_computing_D4N.g");
```
Examples 0-6 finish in a few seconds, while 7,8,9 include research-level problems and may take a few minutes.

## Copyright and license

Copyright © Alison Warman for `AlgebrasTQD.g`, the source files `source/1_preliminaries.g` through `source/7_quantum_computing.g`, the files in `examples/`, and this README. All these files are licensed under the Creative Commons Attribution 4.0 International License (CC BY 4.0). See [LICENSE.md](LICENSE.md) or <https://creativecommons.org/licenses/by/4.0/>. When sharing or adapting this material, credit the author Alison Warman.

The exception is `source/0_Modular_Data_Mignard-Schauenburg-Gruen-Morrison.g`. As stated in that file, its first four functions were written by [Michaël Mignard and Peter Schauenburg][mignard2017moritaequivalencepointedfusion], and the rest by [Angus Gruen and Scott Morrison][gruen2021computing]. The author made small changes, to make it compatible and work correctly with the main source files. Copyright in the original code remains with its authors, who must be cited for the `source/0_Modular_Data_Mignard-Schauenburg-Gruen-Morrison.g` file.

## Acknowledgements

The author thanks Yuhan Gai and Sakura Schäfer-Nameki for the collaboration on [Twin Algebras][Gai:2026hjk] and [Twin Phases][Warman:2026gfz] that motivated this code, and Xiao-Gang Wen for suggesting GAP. The quantum computing code reproduces results of [Hybrid Lattice Surgery][Huang:2025ump] and [Constant-Depth Clifford-Hierarchy Gates][Warman:2025hov].

Anthropic's Claude Fable 5.1 and Opus 5.5, and OpenAI's Codex GPT-6 Sol, were used to check the code and suggest improvements. The author independently reviewed and verified all AI-assisted output and takes full responsibility for the AlgebrasTQD code.

This work is supported by the UKRI Frontier Research Grant underwriting the ERC Advanced Grant “Generalized Symmetries in Quantum Field Theory and Quantum Gravity”.

[gruen2021computing]: https://arxiv.org/abs/1808.05060
[mignard2017moritaequivalencepointedfusion]: https://arxiv.org/abs/1708.06538
[Gai:2026hjk]: https://arxiv.org/abs/2605.31602
[Warman:2026gfz]: https://arxiv.org/abs/2605.31601
[Huang:2025ump]: https://arxiv.org/abs/2510.20890
[Warman:2025hov]: https://arxiv.org/abs/2512.13777
[davydov2017lagrangian]: https://arxiv.org/abs/1603.04650
