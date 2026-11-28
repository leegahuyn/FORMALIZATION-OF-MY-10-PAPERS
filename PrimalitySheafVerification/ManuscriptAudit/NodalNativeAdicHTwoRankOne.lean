import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeFiniteHTwoNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHTwoInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHTwoNormalization
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicResidueScalar
import PrimalitySheafVerification.ManuscriptAudit.NodalFiniteCompactHTwoNormalization

/-! The actual continuous degree-two nodal cohomology is free of rank
one, via the genuine cyclic residue system. The same computation
applies to the normalization and to the smooth affine compact group. -/

namespace ManuscriptAudit.NodalNativeAdicHTwoRankOne

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalAffineSmoothCompactOpen (compactOpen)
open NodalNativeFiniteHTwoNormalization (levelEquiv step_surjective preservesEpimorphisms)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees (nativeStep reductionMap)
open ProetaleContinuousDirectImageMaps (functions)
open OpenProetaleExtension (extensionByZero)
open NativeAdicScalarAction (adicModule scalarMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h₂ : (2 : K) ≠ 0)
  (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private abbrev X := projectiveNode K
private abbrev Y := normalizedNode K
private abbrev G (n : ℕ) := Sheaf.H (finiteCoefficient (X K) l n) 2
private abbrev t := nativeStep (X K) l 2
private abbrev c := CyclicPowerInverseLimit.coordinates l (G K l) (t K l)
  (step_surjective K h₂ l) (levelEquiv K h₂ l)

private def properAddEquiv : (X K).EllAdicCohomology l 2 ≃+ ℤ_[l] :=
  (NodalNativeAdicHTwoInverseLimit.reductionEquiv K h₂ l).trans
    (CyclicPowerInverseLimit.padicEquiv l (G K l) (t K l)
      (step_surjective K h₂ l) (levelEquiv K h₂ l))

private theorem evaluation (n : ℕ) (x : (X K).EllAdicCohomology l 2) :
    PadicInt.toZModPow n (properAddEquiv K h₂ l x) =
      c K h₂ l n ((reductionMap (X K) l 2 x).val n) :=
  CyclicPowerInverseLimit.padicEquiv_evaluation l (G K l) (t K l)
    (step_surjective K h₂ l) (levelEquiv K h₂ l) n
    (NodalNativeAdicHTwoInverseLimit.reductionEquiv K h₂ l x)

local instance : Module ℤ_[l] ((X K).EllAdicCohomology l 2) := adicModule (X K) l 2
local instance : Module ℤ_[l] ((Y K).EllAdicCohomology l 2) := adicModule (Y K) l 2

set_option maxHeartbeats 6300000 in
/-- The proper nodal curve's actual native adic group has rank one. -/
def properLinearEquiv : (X K).EllAdicCohomology l 2 ≃ₗ[ℤ_[l]] ℤ_[l] where
  __ := properAddEquiv K h₂ l
  map_smul' r x := by
    apply (PadicResidueSystems.padicRingEquiv l).injective
    apply Subtype.ext
    funext n
    change PadicInt.toZModPow n (properAddEquiv K h₂ l (r • x)) =
      PadicInt.toZModPow n (r * properAddEquiv K h₂ l x)
    rw [map_mul, evaluation, evaluation]
    let u := (PadicInt.toZModPow n r).val
    let a := (reductionMap (X K) l 2 x).val n
    have h : (reductionMap (X K) l 2 (r • x)).val n = u • a :=
      NativeAdicResidueScalar.reduction_scalar (X K) l 2 n r x
    calc
      _ = c K h₂ l n (u • a) := congrArg (c K h₂ l n) h
      _ = u • c K h₂ l n a := map_nsmul (c K h₂ l n) a u
      _ = _ := by
        rw [nsmul_eq_mul]
        exact congrArg (fun t ↦ t * c K h₂ l n a) (ZMod.natCast_zmod_val (PadicInt.toZModPow n r))

/-- The normalization's actual intrinsic adic group has rank one. -/
def normalizationLinearEquiv : (Y K).EllAdicCohomology l 2 ≃ₗ[ℤ_[l]] ℤ_[l] := by
  letI := preservesEpimorphisms K h₂
  exact (NodalNativeAdicHTwoNormalization.properEquiv K l h₂).symm.trans
    (properLinearEquiv K h₂ l)

/-- The genuine compactly supported degree-two group of the affine nodal smooth locus. -/
def compactEquiv :
    Sheaf.H ((extensionByZero (compactOpen K) AddCommGrpCat.{1}).obj
      (functions ℤ_[l] _)) 2 ≃+ ℤ_[l] := by
  letI := preservesEpimorphisms K h₂
  exact (NodalNativeAdicHTwoNormalization.compactEquiv K l h₂).trans
    (normalizationLinearEquiv K h₂ l).toAddEquiv

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩
local instance residueOrder (n : ℕ) : NeZero (l ^ n) :=
  ⟨pow_ne_zero n (show l.Prime from Fact.out).ne_zero⟩

/-- The same actual compact-support group at each finite coefficient level. -/
def compactFiniteEquiv (n : ℕ) :
    NodalFiniteCompactHTwoNormalization.compact K (ZMod (l ^ n)) ≃+ ZMod (l ^ n) :=
  (NodalFiniteCompactHTwoNormalization.ambientEquiv K (ZMod (l ^ n))).trans
    (levelEquiv K h₂ l n)

end
end ManuscriptAudit.NodalNativeAdicHTwoRankOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeAdicHTwoRankOne.properLinearEquiv,
      ``ManuscriptAudit.NodalNativeAdicHTwoRankOne.normalizationLinearEquiv,
      ``ManuscriptAudit.NodalNativeAdicHTwoRankOne.compactEquiv,
      ``ManuscriptAudit.NodalNativeAdicHTwoRankOne.compactFiniteEquiv] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
