import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindFloorParity

/-! Lattice-point proof of reciprocity for the half floor sum at any odd coprime moduli. -/

namespace ManuscriptAudit.Paper8DedekindFloorReciprocity

open Finset Paper8DedekindFloorParity

private theorem half_floor_le {h k x : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1)
    (hx : x < k / 2) : h * (x + 1) / k ≤ h / 2 := by
  have hk0 : 0 < k := by omega
  have h1 : h * (x + 1) ≤ h * (k / 2) := Nat.mul_le_mul_left h (by omega)
  have h2 : h * (k / 2) < (h / 2 + 1) * k := by
    have hH : h = 2 * (h / 2) + 1 := by omega
    have hK : k = 2 * (k / 2) + 1 := by omega
    conv_lhs => rw [hH]
    conv_rhs => arg 2; rw [hK]
    nlinarith
  have h3 : h * (x + 1) / k < h / 2 + 1 :=
    (Nat.div_lt_iff_lt_mul hk0).2 (h1.trans_lt h2)
  omega

private theorem half_floor_row_count {h k x : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1)
    (hx : x < k / 2) :
    (∑ y ∈ range (h / 2), if (y + 1) * k ≤ h * (x + 1) then (1 : ℕ) else 0) =
      h * (x + 1) / k := by
  let q := h * (x + 1) / k
  have hk0 : 0 < k := by omega
  have hq : q ≤ h / 2 := half_floor_le hh hk hx
  have hFilter : (range (h / 2)).filter (fun y => (y + 1) * k ≤ h * (x + 1)) = range q := by
    ext y
    simp only [mem_filter, mem_range]
    have hI : (y + 1) * k ≤ h * (x + 1) ↔ y + 1 ≤ q :=
      (Nat.le_div_iff_mul_le hk0).symm
    rw [hI]
    omega
  rw [← Finset.sum_filter, hFilter]
  simp [q]

theorem halfFloorWeight_reciprocity {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1)
    (hC : h.Coprime k) :
    halfFloorWeight h k + halfFloorWeight k h = k / 2 * (h / 2) := by
  have hNo (x : ℕ) (hx : x < k / 2) (y : ℕ) :
      (y + 1) * k ≠ h * (x + 1) := by
    intro he
    have hD : k ∣ h * (x + 1) := ⟨y + 1, by rw [← he, mul_comm]⟩
    have hDx : k ∣ x + 1 := hC.symm.dvd_of_dvd_mul_left hD
    have hLe := Nat.le_of_dvd (Nat.succ_pos x) hDx
    omega
  have hRows (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
      halfFloorWeight a b =
        ∑ x ∈ range (b / 2), ∑ y ∈ range (a / 2),
          if (y + 1) * b ≤ a * (x + 1) then (1 : ℕ) else 0 := by
    unfold halfFloorWeight
    apply sum_congr rfl
    intro x hx
    exact (half_floor_row_count ha hb (mem_range.mp hx)).symm
  rw [hRows h k hh hk, hRows k h hk hh]
  rw [Finset.sum_comm (s := range (h / 2)), ← Finset.sum_add_distrib]
  calc
    _ = ∑ x ∈ range (k / 2), ∑ _y ∈ range (h / 2), (1 : ℕ) := by
      apply sum_congr rfl
      intro x hx
      rw [← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro y _
      have hNE := hNo x (mem_range.mp hx) y
      rw [mul_comm (x + 1) h, mul_comm k (y + 1)]
      by_cases hxy : (y + 1) * k ≤ h * (x + 1)
      · have hyx : ¬ h * (x + 1) ≤ (y + 1) * k := by omega
        simp [hxy, hyx]
      · have hyx : h * (x + 1) ≤ (y + 1) * k := by omega
        simp [hxy, hyx]
    _ = _ := by simp [Nat.mul_comm]

end ManuscriptAudit.Paper8DedekindFloorReciprocity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindFloorReciprocity.halfFloorWeight_reciprocity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
