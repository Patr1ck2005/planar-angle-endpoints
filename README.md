# Near-minimizers of the largest angle in seven- and eight-point planar sets

Lean 4 companion to the manuscript by **Keren Wang**. For seven or eight distinct planar points whose largest angle approaches the classical infimum of 120°, normalize the diameter to one and take a limit of the labelled points.

- Eight points converge to two sites carrying four labels each.
- Seven points converge to two sites carrying three and four labels, or to the circumcenter and vertices of an equilateral triangle, with one label at the circumcenter and two at each vertex.
- Each listed profile occurs.

The manuscript also derives qualitative stability and studies the sharp angle bound for an enclosed cluster and the geometry of equality. The classical seven- and eight-point infima and nonattainment are due to [Erdős and Szekeres, p. 54](https://users.renyi.hu/~p_erdos/1960-09.pdf#page=2). The local direction count is closely related to [Sendov, Lemma 3.7](https://doi.org/10.1007/BF01874605).

## Statements and sources

The classification is formalized using [attainable weighted supports](lean/seven-eight/src/WeightedLabels.lean). Use each package's `CheckPublic.lean` to inspect the statements and their axiom dependencies.

| Manuscript result | Lean declaration |
| --- | --- |
| Eight-point classification | [`R90.Endpoint.eight_shape`](lean/seven-eight/src/EndpointShapes.lean) |
| Seven-point classification, including equilateral and circumcenter conditions | [`R90.Endpoint.seven_geometry`](lean/seven-eight/src/SevenEightEndpointResearch.lean) |
| Two-site and four-site realizations | [`R90.Endpoint.two_centers`](lean/seven-eight/src/TwoEndpointSites.lean), [`R92.Seven.attainable_seven`](lean/seven-eight/src/SevenFourCenters.lean) |
| Uniform excess with five separated points | [`R87.Stability.five_separated_endpoint`](lean/seven-eight/src/FiveSeparatedEndpoint.lean) |
| Balanced eight-point stability | [`R88.Stability.eight_near_endpoint`](lean/seven-eight/src/EightPointClusters.lean) |
| Sharp enclosed-cluster angle and number of sites at equality | [`R89.Sharp.sharp`](lean/enclosed/src/EnclosedSharp.lean), [`R89.Sharp.equality_four`](lean/enclosed/src/EnclosedRigidity.lean) |
| Strict excess with five separated sites around an enclosed cluster | [`R94.Enclosed.surrounded_minimum_gap`](lean/enclosed/src/SelectedInteriorGap.lean) |

## Reproduce the checks

Install [Elan](https://lean-lang.org/install/), Git and Python 3. Each directory is a separate Lake project with Lean `v4.34.0` and dependencies pinned in its `lake-manifest.json`.

Run from `lean/seven-eight` for the classification. Run the same commands from `lean/enclosed` for the enclosed-cluster results. Use `python3` if your system uses that command for Python 3.

```sh
python verify_bundle.py
python cache_inputs.py
python build_serial.py
python check_public.py
```

The cache step fetches mathlib object files for the external imports. The serial build compiles the project sources, and the last command reimports the six exposed declarations and compares their axiom reports. The original source ZIPs at [v1.0.0](https://github.com/Patr1ck2005/planar-angle-endpoints/releases/tag/v1.0.0) have hashes in [SHA256SUMS](SHA256SUMS).

The [archived kernel receipts](verification) record the checks using extracted sources and pinned dependency objects. Each exposed declaration used only `propext`, `Classical.choice` and `Quot.sound`. This release repackages those exact project files. The complete cold build on a second machine remains unverified.

The original [classification notices](lean/seven-eight/notices) and [enclosure notices](lean/enclosed/notices) preserve attribution and upstream license texts. AI-assisted development included proof exploration, Lean implementation and drafting.
