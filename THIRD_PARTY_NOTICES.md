# Third-party material

The FLMF source snapshot is distributed under the Apache License 2.0 in LICENSE.
The original source notices are retained without alteration.

The Watson implementation in `FLMF/Support/Watson.lean` originates from
Picard–Lefschetz and is by Michael R. Douglas, copyright 2026, distributed
under Apache License 2.0. Its original copyright and author notices remain
in the source. The Apache License 2.0 is included in
[LICENSE](LICENSE). The original license copy also remains locally in the
Git-ignored `docs/PICARD_LEFSCHETZ_LICENSE`.
The original source revision, path, and checksum are retained in
`numerical check/source_manifest.json`.

On 2026-10-14 the module was integrated into FLMF's support sources, replacing
the separate vendored Lake package. Declaration names and proofs are unchanged;
only the module location and documentation changed.

Mathlib and its dependencies are fetched separately through Lake. Their own
licenses and notices apply; their source and compiled caches are not included
in this release folder.

DLMF equation identifiers and links identify the mathematical reference:
NIST Digital Library of Mathematical Functions, Chapter 7, Error Functions,
Dawson's and Fresnel Integrals, https://dlmf.nist.gov/7.
The historical evidence files preserve excerpts and review outputs from the
FLMF verification process. They do not represent a new DLMF release or an
endorsement by NIST.
