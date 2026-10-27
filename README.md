# ai-formalized

AI-assisted, machine-checked solutions to mathematics and physics problems in Lean 4.

Built on [Physlib](https://github.com/leanprover-community/physlib) and Mathlib.

Each problem lives in its own folder: an independent Lake project (with its own pinned
Physlib/Mathlib versions), the Lean sources, and a short paper.

| Folder | Problem | Status |
|---|---|---|
| [`kepler-lrl/`](kepler-lrl/) | Kepler problem: conservation of the Laplace–Runge–Lenz vector and Kepler's first law | Complete, no `sorry` · [paper](kepler-lrl/paper/main.pdf) |

## Building a problem

```bash
cd <folder>
lake exe cache get   # prebuilt Mathlib
lake build
```

## Adding a problem

Create a new folder with its own `lakefile.toml`, `lean-toolchain`, Lean sources, `README.md`
and `paper/`, and add a row to the table above.

## Authors

Nichlas Löfdahl and Claude (Anthropic).

## License

Apache 2.0 (see `LICENSE`).
