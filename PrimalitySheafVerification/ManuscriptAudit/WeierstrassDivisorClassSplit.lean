import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassDivisorDegree

/-! The actual geometric divisor class group splits into the affine ideal
class group and the integer degree at the rational point at infinity. -/

namespace ManuscriptAudit.WeierstrassDivisorClassSplit

open FractionalIdeal WeierstrassCurve.Affine WeierstrassFractionalIdealDegree
open WeierstrassDivisorDegree
open scoped nonZeroDivisors

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev A := W.CoordinateRing
private abbrev F := W.FunctionField
private abbrev P := toPrincipalIdeal (A W) (F W)
private abbrev D := Divisors W
private abbrev Q := DivisorClassGroup W
private abbrev Affine := (FractionalIdeal (A W)⁰ (F W))ˣ ⧸ (P W).range

private abbrev project (x : D W) : Q W := QuotientGroup.mk' (principal W).range x
private abbrev projectAffine (I : (FractionalIdeal (A W)⁰ (F W))ˣ) : Affine W :=
  QuotientGroup.mk' (P W).range I

/-- Restriction discards the point at infinity and passes to the actual
affine fractional-ideal class. -/
def affineProjection : Q W →* Affine W :=
  QuotientGroup.lift (principal W).range
    ((QuotientGroup.mk' (P W).range).comp (MonoidHom.fst _ _)) (by
      intro d hd
      obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hd
      change projectAffine W ((P W) f) = 1
      exact (QuotientGroup.eq_one_iff ((P W) f)).mpr ⟨f, rfl⟩)

private theorem affineProjection_mk (d : D W) :
    affineProjection W (project W d) = projectAffine W d.1 := by
  unfold affineProjection
  rw [QuotientGroup.lift_mk'] <;> rfl

private theorem classDegree_mk (d : D W) :
    classDegree W (project W d) = divisorDegree W d := by
  unfold classDegree
  rw [QuotientGroup.lift_mk']

private def comparison : Q W →* Affine W × Multiplicative ℤ :=
  (affineProjection W).prod (classDegree W)

private theorem comparison_injective : Function.Injective (comparison W) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (principal W).range a
  have hAff : projectAffine W d.1 = 1 :=
    (affineProjection_mk W d).symm.trans (congrArg Prod.fst ha)
  have hDeg : divisorDegree W d = 1 :=
    (classDegree_mk W d).symm.trans (congrArg Prod.snd ha)
  obtain ⟨f, hf⟩ := (QuotientGroup.eq_one_iff d.1).mp hAff
  let p := principal W f
  have hP : project W p = 1 := (QuotientGroup.eq_one_iff p).mpr ⟨f, rfl⟩
  have hPDeg : divisorDegree W p = 1 := by
    rw [← classDegree_mk, hP, map_one]
  have h1 : d.1 = p.1 := hf.symm
  have h2 : d.2 = p.2 := by
    have h := congrArg Multiplicative.toAdd (hDeg.trans hPDeg.symm)
    change fractionalDegree W d.1.val + d.2.toAdd =
      fractionalDegree W p.1.val + p.2.toAdd at h
    rw [h1] at h
    exact Multiplicative.toAdd.injective (add_left_cancel h)
  have hd : d = p := Prod.ext h1 h2
  exact (QuotientGroup.eq_one_iff d).mpr (hd.symm ▸ (show p ∈ (principal W).range from ⟨f, rfl⟩))

private theorem comparison_surjective : Function.Surjective (comparison W) := by
  rintro ⟨a, n⟩
  obtain ⟨I, hI⟩ := QuotientGroup.mk'_surjective (P W).range a
  let d : D W := (I, Multiplicative.ofAdd (n.toAdd - fractionalDegree W I.val))
  refine ⟨project W d, Prod.ext ?_ ?_⟩
  · change affineProjection W (project W d) = a
    rw [affineProjection_mk]
    exact hI
  · change classDegree W (project W d) = n
    rw [classDegree_mk]
    apply Multiplicative.toAdd.injective
    change fractionalDegree W I.val + (n.toAdd - fractionalDegree W I.val) = n.toAdd
    rw [add_comm, sub_add_cancel]

/-- The geometric divisor class is specified by its affine class and
its actual integer degree. -/
def classGroupSplit : Q W ≃* ClassGroup (A W) × Multiplicative ℤ :=
  (MulEquiv.ofBijective (comparison W) ⟨comparison_injective W, comparison_surjective W⟩).trans
    ((ClassGroup.equiv (R := A W) (F W)).symm.prodCongr (MulEquiv.refl (Multiplicative ℤ)))

end

end ManuscriptAudit.WeierstrassDivisorClassSplit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassDivisorClassSplit.classGroupSplit
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
