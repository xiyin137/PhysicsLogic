# String Book Unit Notes

Each file in this directory corresponds to one top-level unit from the book:
- `section-XX.md` for numbered sections
- `appendix-x.md` for appendices

## Intended Use
For each unit, record:
- concise reading summary
- candidate formalization units
- assumptions to introduce or reuse
- extraction checklist completion

## Progress Snapshot (2026-03-01)
- `43/44` units are marked `initial extraction complete`.
- Completed set so far:
  - sections: `01`, `02`, `03`, `04`, `05`, `06`, `07`, `08`, `09`, `10`, `11`, `12`, `13`, `14`, `15`, `16`, `17`, `18`, `20`, `21`, `22`, `23`, `24`, `25`, `26`
  - appendices: `A`, `B`, `C`, `D`, `E`, `F`, `G`, `H`, `I`, `J`, `K`, `L`, `M`, `N`, `O`, `P`, `Q`, `R`
- Current emphasis: appendices that feed `PhysicsLogic/QFT/*` lanes.

## Naming Convention
- When possible, list assumption candidates using prospective `AssumptionId`-style
  keys so migration into `PhysicsLogic/Assumptions.lean` is direct.

## Regeneration Behavior
`./scripts/stringbook_sync_notes.sh` creates missing templates but does not
overwrite existing note files by default.

Use force mode only when intentionally resetting templates:

```bash
STRINGBOOK_FORCE_REWRITE=1 ./scripts/stringbook_sync_notes.sh
```
