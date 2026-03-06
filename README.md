# Arboretum.hs

*A Haskell library for symbolic computation in algebras of trees and forests.*

**Arboretum** is a Haskell library for algebraic computations involving trees and forests, designed to support research in areas such as numerical analysis, rough path theory, regularity structures, and non-associative algebra.

This package provides a flexible and extensible framework for working with algebras of graphs, including the implementation of decorated trees, aromatic forests, and operations such as grafting and substitution. It also supports symbolic computation in graded vector spaces. In addition, the package can generate LaTeX code and corresponding PDF output to visualize decorated aromatic forests and other elements of vector spaces, facilitating the interpretation of computation results.

## Motivation

Many modern mathematical frameworks use trees and forests as a foundational combinatorial structure. From the Butcher group in numerical analysis to the branched rough paths and regularity structures in stochastic analysis, trees encode the composition of operations, hierarchical dependencies, and renormalization procedures. Arboretum offers a unified platform for prototyping and computing in these contexts.

## Getting Started

Prerequisites: stack.

```bash
git clone https://github.com/ebronasco/arboretum.hs.git
cd arboretum.hs
stack build
```

## Documentation and examples

The manual can be found in the **manual** directory.

The reference documentation is found in **docs** directory. To read it open the **index.html** file in a web browser.

### Examples

| Structure | Example |
|---|---|
| Concatenation–Deshuffle Hopf algebra | [`ConcatDeshuffle.hs`](examples/ConcatDeshuffle.hs) |
| Shuffle–Deconcatenation Hopf algebra | [`ShuffleDeconcat.hs`](examples/ShuffleDeconcat.hs) |
| Grossman–Larson Hopf algebra over planar forests | [`PlanarGrossmanLarson.hs`](examples/PlanarGrossmanLarson.hs) |
| Connes–Kreimer Hopf algebra over planar forests | [`PlanarConnesKreimer.hs`](examples/PlanarConnesKreimer.hs) |
| Cosubstitution of planar forests | [`Cosubstitution.hs`](examples/Cosubstitution.hs) |
| Lie–Butcher series of the exact solution | [`LieButcherExact.hs`](examples/LieButcherExact.hs) |
| Grossman–Larson Hopf algebra over non-planar forests | [`NonplanarGrossmanLarson.hs`](examples/NonplanarGrossmanLarson.hs) |
| Connes-Kreimer Hopf algebra over non-planar forests | [`NonplanarConnesKreimer.hs`](examples/NonplanarConnesKreimer.hs) |
| Butcher series of the exact solution | [`ButcherExact.hs`](examples/ButcherExact.hs) |
| Butcher series of Runge-Kutta methods | [`RungeKutta.hs`](examples/RungeKutta.hs) |
| Divergence, grafting, Grossman-Larson, and substitution of aromatic forests | [`AromaticForests.hs`](examples/AromaticForests.hs) |
| Construction and grafting of arbitrary graphs | [`Graph.hs`](examples/Graph.hs) |


## References

- Eugen BRONASCO (2025) *Algebraic structures and numerical methods for invariant measure sampling of Langevin dynamics*. Doctoral Thesis.
- Eugen BRONASCO, Jean-Luc FALCONE, Gilles VILMART (in preparation) *Arboretum.hs: Symbolic manipulation for algebras of graphs*.

## Contributing

Contributions are welcome! Please:

1. Fork the repository  
2. Create a new branch  
3. Commit your changes  
4. Open a pull request  

## License

This project is licensed under the **BSD 3-Clause "New" or "Revised" License**. See the `LICENSE` file for details.

## Development

- **Autoformatting**:  
  `fourmolu -i <file-name>`  
  Configuration is specified in `fourmolu.yaml`.

- **Linting**:  
  `hlint <file-name>`

- **Documentation**:  
  Generated with `haddock`.

- **Testing**:  
  Uses `doctest` and `QuickCheck`.
