# Changelog

## v0.1.2 (2026-10-13)

- Licensed under Apache-2.0, with a `LICENSE` file and a copyright header on every source file.
- Licence, description and keywords in `lakefile.toml`.
- A small test suite (`lake test`), run in CI in place of the benchmarks.
- Removed editor and MCP configuration from the repository.

## v0.1.1 (2026-10-13)

- Benchmarks in `bench/` for compiled evaluation and kernel proofs (`lake build Bench`).
- README sections on the algorithm and its performance.

## v0.1.0 (2026-10-12)

First release.

- `AdjList.reaches`: breadth-first search, proved to decide `Relation.TransGen` (`reaches_iff`).
- `Decidable` instances for `TransGen` and `ReflTransGen` of any decidable relation on a finite
  type, which work with `decide`.
- `AdjList.shortest`: shortest walks, with `shortest_fullWalk`, `shortest_le` and
  `shortest_eq_none_iff`.
- Conversions to and from Mathlib's `Digraph`.
