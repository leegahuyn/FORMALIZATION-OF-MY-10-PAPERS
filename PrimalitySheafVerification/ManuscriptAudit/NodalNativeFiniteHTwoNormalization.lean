import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleProperNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeFiniteHTwoNormalizerImage
import PrimalitySheafVerification.ManuscriptAudit.ProetaleExactDirectImageNaturality
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeFiniteHTwo
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeHTwoTransition

/-! The actual native normalization equivalence in finite degree two
commutes with residue reduction, giving the cyclic levels and onto
transitions on the proper nodal curve. -/

namespace ManuscriptAudit.NodalNativeFiniteHTwoNormalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizationMap normalizedNode)
open ProetaleBaseChange (directImage)
open ProetaleContinuousDirectImageMaps (diagonal functions)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees (nativeStep)
open ProetaleExactDirectImageCohomology (continuousEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h₂ : (2 : K) ≠ 0)
  (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private abbrev X := projectiveNode K
private abbrev Y := normalizedNode K
private abbrev f := normalizationMap K
private abbrev A := AddCommGrpCat.{1}
private abbrev P := directImage (f K) A

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩
local instance modulus_neZero (n : ℕ) : NeZero (l ^ n) :=
  ⟨pow_ne_zero n (show l.Prime from Fact.out).ne_zero⟩

/-- The actual normalization direct image is exact in the native coefficient universe. -/
theorem preservesEpimorphisms : (P K).PreservesEpimorphisms where
  preserves g := NodalProetaleProperNormalization.map_epi K h₂ g

private abbrev F (n : ℕ) := ZMod (l ^ n)

/-- The degree-two comparison uses the actual proper normalization map. -/
def comparison (n : ℕ) :
    Sheaf.H (finiteCoefficient (X K) l n) 2 ≃+ Sheaf.H (finiteCoefficient (Y K) l n) 2 := by
  letI := preservesEpimorphisms K h₂
  exact (NodalNativeFiniteHTwoNormalizerImage.normalizationImageEquiv K (F l n) h₂).trans
    (continuousEquiv (f K) (F l n) 2)

private abbrev σ (T : Scheme.{0}) (n : ℕ) :=
  (ProetaleCoefficientUniverseLift.lift T).map (ProetaleResidueSheaves.residueTransition T l n)

set_option maxHeartbeats 5900000 in
/-- The genuine comparison commutes with the actual residue transition. -/
theorem comparison_natural (n : ℕ) (x : Sheaf.H (finiteCoefficient (X K) l (n + 1)) 2) :
    comparison K h₂ l n (nativeStep (X K) l 2 n x) =
      nativeStep (Y K) l 2 n (comparison K h₂ l (n + 1) x) := by
  letI := preservesEpimorphisms K h₂
  let a := σ l (X K) n
  let b := σ l (Y K) n
  let i := diagonal (F l n) (f K)
  let j := diagonal (F l (n + 1)) (f K)
  have hn : a ≫ i = j ≫ (P K).map b :=
    ProetaleContinuousCoefficientNaturality.diagonal_natural
      (PadicResidueSystems.reduction l (Nat.le_succ n)).toAddMonoidHom
      continuous_of_discreteTopology (f K)
  change continuousEquiv (f K) (F l n) 2
      (Sheaf.H.map i 2 (Sheaf.H.map a 2 x)) =
    Sheaf.H.map b 2 (continuousEquiv (f K) (F l (n + 1)) 2 (Sheaf.H.map j 2 x))
  rw [← Sheaf.H.map_comp_apply, hn, Sheaf.H.map_comp_apply]
  exact ProetaleExactDirectImageNaturality.natural (f K) b 2 (Sheaf.H.map j 2 x)

/-- The proper nodal curve has the same actual cyclic finite-level group. -/
def levelEquiv (n : ℕ) :
    Sheaf.H (finiteCoefficient (X K) l n) 2 ≃+ ZMod (l ^ n) :=
  (comparison K h₂ l n).trans (NodalNormalizedNativeFiniteHTwo.finiteEquiv K h₂ l n).symm

/-- Each actual proper nodal degree-two residue transition is onto. -/
theorem step_surjective (n : ℕ) : Function.Surjective (nativeStep (X K) l 2 n) := by
  intro x
  let e := comparison K h₂ l n
  let e' := comparison K h₂ l (n + 1)
  obtain ⟨y, hy⟩ := NodalNormalizedNativeHTwoTransition.step_surjective K l h₂ n (e x)
  refine ⟨e'.symm y, e.injective ?_⟩
  rw [show e = comparison K h₂ l n from rfl, comparison_natural]
  change nativeStep (Y K) l 2 n (e' (e'.symm y)) = e x
  rwa [e'.apply_symm_apply]

end
end ManuscriptAudit.NodalNativeFiniteHTwoNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeFiniteHTwoNormalization.comparison,
      ``ManuscriptAudit.NodalNativeFiniteHTwoNormalization.comparison_natural,
      ``ManuscriptAudit.NodalNativeFiniteHTwoNormalization.levelEquiv,
      ``ManuscriptAudit.NodalNativeFiniteHTwoNormalization.step_surjective] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
