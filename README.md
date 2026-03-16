# constrained-decoding-formalization

[Flexible and Efficient Grammar-Constrained Decoding](https://arxiv.org/pdf/2502.05111)

## Dependency Visualizer

This repo includes a CLI for generating and hosting a declaration dependency graph from `lean4export`:

```bash
./lean-dep-viz serve
```

On startup, the CLI:

- builds the Lean project with `lake build`
- builds `lean4export` from the repo's Lake dependency
- exports the reachable declarations under the root library
- serves the frontend at `/` and the generated graph JSON at `/graph-data`

The first run can take a while because it needs to build both the project and the exporter.

Useful options:

```bash
./lean-dep-viz serve --port 8765
./lean-dep-viz serve --host 0.0.0.0 --port 8765
./lean-dep-viz serve --open
./lean-dep-viz serve --module ConstrainedDecodingFormalization
./lean-dep-viz serve --lean4export-bin /path/to/lean4export
```

The server exposes the visualizer at `/` and `/lean-dep-viz.html`, the generated graph at `/graph-data`, and a simple `/healthz` endpoint.
