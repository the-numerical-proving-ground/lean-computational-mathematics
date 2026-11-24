# Architecture of the certified tridiagonal foundations

The twelve modules introduced in `7cfe1d9b35ebec262e26325810d1f156d777b74c` supply reusable
matrix and floating-point results. Exact tier entries classify those modules
as reusable. The requested adjacent-gap target and proof inherit the source
tier. The existing analysis and source aggregates make both groups reachable
from the complete library.

`Analysis.OperatorNorms.RealMatrix` already owns declarations. The new
Euclidean action lemmas move from its `RealMatrix/Euclidean.lean` child to
`OperatorNorms/RealMatrixEuclidean.lean` so the established owner can retain
its import path. The move adds a module docstring and preserves the theorem
statements and proof bodies. `Analysis.MatrixNorms.Nuclear.Basic` changes one
import to follow the move. These two mechanically changed files have the
following SHA-256 hashes.

| File | At the reuse commit | At this checkpoint |
| --- | --- | --- |
| Euclidean action lemmas | `d3c1cbe80cf671b722a9997fcdb23dc52947a89760776da6a8d9effa192cb69d` | `c7a15cf369b8030e807d27fcfcd8c37cbaa3f93250e01be21ec10d9bd1e51747` |
| Nuclear norm lemmas | `3c52ac4792ed72c085b75fad3d16a5568035b2c479634dd32361d66d8f2a1bb8` | `ee190c8865d0b7dea0f386a82105a3f5624d8b1a2d6a41558ba975dbb16a9fb0` |
