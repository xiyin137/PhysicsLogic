# String Book Workspace

This directory tracks the systematic extraction of the local string-book source
materials into formalization-ready notes for `PhysicsLogic`.

## Files
- `inventory.md`: generated snapshot of source assets and counts.
- `reading-index.md`: generated unit index (sections/appendices) and notebook map.
- `ROADMAP.md`: phased incorporation plan and quality gates.
- `appendix-qft-crosswalk.md`: mapping from appendices to `PhysicsLogic/QFT` targets.
- `physics-organization.md`: physics-first lane organization for formalization.
- `reference-artifacts.md`: tracked index for gitignored notebook/figure artifacts
  under `references/stringbook/` and their Lean touchpoints.
- `data/`: generated machine-readable TSV extracts from the book TOC.
- `notes/`: per-unit note templates for manual extraction and progress tracking.

## Current Focus
- Prioritize appendices that directly harden QFT foundations (`B` through `F`).
- Keep chapter order as provenance only; place Lean declarations by physics lane.
- Treat path-integral actions with complex-valued interfaces when modeling general
  Lorentzian or contour-deformed quantum amplitudes.

## Regeneration
Run:

```bash
./scripts/stringbook_sync_notes.sh
```

To force-rewrite note templates (use only when you intentionally want to reset
existing note content):

```bash
STRINGBOOK_FORCE_REWRITE=1 ./scripts/stringbook_sync_notes.sh
```
