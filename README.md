# constrained-decoding-formalization

[Flexible and Efficient Grammar-Constrained Decoding](https://arxiv.org/pdf/2502.05111)

## Dependency Visualizer

This repo includes a small CLI for locally hosting [`lean-dep-viz.html`](lean-dep-viz.html):

```bash
./lean-dep-viz serve
```

Useful options:

```bash
./lean-dep-viz serve --port 8765
./lean-dep-viz serve --host 0.0.0.0 --port 8765
./lean-dep-viz serve --open
```

The server exposes the visualizer at `/` and `/lean-dep-viz.html`, plus a simple `/healthz` endpoint.
