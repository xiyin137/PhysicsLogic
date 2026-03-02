# PhysicsLogic Agent Guidelines

## Physics-First Principle
- Prioritize physically meaningful content and interfaces over maximal mathematical foundations.
- Use the minimum formal machinery needed to represent the physics claim clearly and correctly.

## Modeling Rules
- Encode unresolved physics statements as explicit claim fields (`Prop`-typed), not `Bool` checklists.
- Keep object semantics correct:
  - states/operators are not scalar numbers;
  - actions are functionals (and may be complex-valued in QFT path integrals).
- Prefer symmetry- and invariance-aware interfaces (gauge, diffeomorphism/reparameterization, Lorentz, Euclidean translation + rotation).
- Avoid trivial or definitional constants (for example, no “critical dimension” definitions that only restate a fixed value).

## String Book Integration
- Use reading notes as an index, but consult the source (`.tex` / PDF / notebooks) for details before encoding claims.
- Import appendix material that is physics-relevant for both string theory and QFT modules.
- Keep documentation in each affected folder up to date as interfaces are hardened.
