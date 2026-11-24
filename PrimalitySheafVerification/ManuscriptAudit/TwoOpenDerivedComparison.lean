import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.Tactic.NormNum

/-!
Paper 4, physical p. 114, Proposition 3.19(iii), uses a comparison on fixed
principal-open covers. For an actual Mayer-Vietoris square the degree-zero
cokernel identifies with the kernel of restriction in degree one.

Physical pp. 105 and 116 take the opens D(M) and D(p). When p divides M
these opens are nested, and the genuine degree-one Čech cokernel is zero.
-/

namespace ManuscriptAudit.TwoOpenDerivedComparison

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace

noncomputable section

section Derived

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

private theorem zeroRange_eq_connectingKer :
    (S.fromBiprod F 0).hom.range = (S.δ F 0 1 rfl).hom.ker := by
  let c := ShortComplex.mk (S.fromBiprod F 0) (S.δ F 0 1 rfl)
    (S.fromBiprod_δ F 0 1 rfl)
  have h : c.Exact := (S.sequence_exact F 0 1 rfl).exact' 1 2 3
  exact h.ab_range_eq_ker

private theorem connectingRange_eq_oneKer :
    (S.δ F 0 1 rfl).hom.range = (S.toBiprod F 1).hom.ker := by
  let c := ShortComplex.mk (S.δ F 0 1 rfl) (S.toBiprod F 1)
    (S.δ_toBiprod F 0 1 rfl)
  have h : c.Exact := (S.sequence_exact F 0 1 rfl).exact' 2 3 4
  exact h.ab_range_eq_ker

/-- The degree-zero restriction cokernel is the subgroup of native degree-one
derived classes whose restrictions to both pieces vanish. -/
def coker_equiv_derivedRestrictionKer :
    ((F.H' 0 S.X₁) ⧸ (S.fromBiprod F 0).hom.range) ≃+
      (S.toBiprod F 1).hom.ker := by
  rw [zeroRange_eq_connectingKer S F, ← connectingRange_eq_oneKer S F]
  exact QuotientAddGroup.quotientKerEquivRange (S.δ F 0 1 rfl).hom

/-- The native connecting map reaches all degree-one derived classes exactly
when their joint restriction to the two pieces is zero. -/
theorem connecting_surjective_iff :
    Function.Surjective (S.δ F 0 1 rfl) ↔ S.toBiprod F 1 = 0 := by
  constructor
  · intro hs
    apply AddCommGrpCat.ext
    intro y
    obtain ⟨x, rfl⟩ := hs y
    change S.toBiprod F 1 ((S.δ F 0 1 rfl) x) = 0
    rw [← AddCommGrpCat.comp_apply, S.δ_toBiprod] <;> rfl
  · intro hr y
    have hy : y ∈ (S.toBiprod F 1).hom.ker := by
      rw [hr] <;> rfl
    rw [← connectingRange_eq_oneKer S F] at hy
    exact hy

end Derived

section OpenSets

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- The actual restriction difference for the two-open Čech complex. -/
def twoOpenDifferential (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) (U V : Opens X) :
    (F.obj (op U) × F.obj (op V)) →+ F.obj (op (U ⊓ V)) where
  toFun s := (F.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) s.1 -
    (F.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op) s.2
  map_zero' := by simp
  map_add' a b := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- A nested two-open cover has surjective restriction difference for any
presheaf of abelian groups, even before imposing a sheaf condition. -/
theorem twoOpenDifferential_surjective_of_le
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) {U V : Opens X} (h : U ≤ V) :
    Function.Surjective (twoOpenDifferential F U V) := by
  have hback : U ≤ U ⊓ V := by rw [inf_eq_left.mpr h]
  let r : op U ⟶ op (U ⊓ V) := (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
  let i : op (U ⊓ V) ⟶ op U := (homOfLE hback).op
  have hi : i ≫ r = 𝟙 (op (U ⊓ V)) := Subsingleton.elim _ _
  intro c
  refine ⟨(F.map i c, 0), ?_⟩
  change F.map r (F.map i c) -
      (F.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op) 0 = c
  rw [map_zero, sub_zero, ← AddCommGrpCat.comp_apply, ← F.map_comp, hi, F.map_id,
    AddCommGrpCat.id_apply]

/-- The cokernel of the two actual restrictions is trivial on nested opens. -/
theorem twoOpenCech1_subsingleton_of_le
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) {U V : Opens X} (h : U ≤ V) :
    Subsingleton ((F.obj (op (U ⊓ V))) ⧸ (twoOpenDifferential F U V).range) := by
  rw [AddMonoidHom.range_eq_top.mpr (twoOpenDifferential_surjective_of_le F h)]
  exact QuotientAddGroup.subsingleton_quotient_top

end OpenSets

section Arithmetic

universe v

/-- A shared divisor makes the two principal opens nested. -/
theorem principalOpens_le_of_dvd {M p : ℤ} (h : p ∣ M) :
    PrimeSpectrum.basicOpen M ≤ PrimeSpectrum.basicOpen p := by
  obtain ⟨r, rfl⟩ := h
  exact PrimeSpectrum.basicOpen_mul_le_left p r

/-- The actual arithmetic square covers D(M) union D(p). -/
def arithmeticSquare (M p : ℤ) :
    (Opens.grothendieckTopology (PrimeSpectrum ℤ)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare (PrimeSpectrum.basicOpen M) (PrimeSpectrum.basicOpen p)

/-- On the shared-divisor locus that union is just D(p). -/
theorem arithmeticSquare_union_of_dvd {M p : ℤ} (h : p ∣ M) :
    (arithmeticSquare M p).X₄ = PrimeSpectrum.basicOpen p := by
  change PrimeSpectrum.basicOpen M ⊔ PrimeSpectrum.basicOpen p = _
  exact sup_eq_right.mpr (principalOpens_le_of_dvd h)

/-- For the printed M=6, p=3, k=2 example, genuine restriction maps on
D(6) and D(3) cannot have degree-one Čech cokernel Z/3. -/
theorem paper4_genuine_sharedPrimeCech_ne_zmod_three
    (F : (Opens (PrimeSpectrum ℤ))ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    ¬ Nonempty
      (((F.obj (op (PrimeSpectrum.basicOpen (6 : ℤ) ⊓ PrimeSpectrum.basicOpen (3 : ℤ)))) ⧸
          (twoOpenDifferential F (PrimeSpectrum.basicOpen (6 : ℤ))
            (PrimeSpectrum.basicOpen (3 : ℤ))).range) ≃+ ZMod 3) := by
  letI := twoOpenCech1_subsingleton_of_le F (principalOpens_le_of_dvd (by norm_num : (3 : ℤ) ∣ 6))
  rintro ⟨e⟩
  exact zero_ne_one (e.symm.injective (Subsingleton.elim (e.symm 0) (e.symm 1)))

end Arithmetic

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``coker_equiv_derivedRestrictionKer, ``connecting_surjective_iff,
      ``twoOpenDifferential_surjective_of_le, ``twoOpenCech1_subsingleton_of_le,
      ``principalOpens_le_of_dvd, ``arithmeticSquare_union_of_dvd,
      ``paper4_genuine_sharedPrimeCech_ne_zmod_three] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.TwoOpenDerivedComparison
