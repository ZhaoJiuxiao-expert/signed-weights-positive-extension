import Lake
open Lake DSL

package rhPaperFormalization

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d7317655e2826dc1f1de9a0c138db2775c4bb841"

@[default_target]
lean_lib Paper where
  roots := #[`PaperFourier, `Orthogonality, `FourierWindow, `PrimeWindow, `Blocks, `PrimeEndpoint, `PrincipalMass, `WindowObstruction, `RademacherBound, `CharacterLowerBound]
