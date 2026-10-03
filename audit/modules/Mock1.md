# Mock1 감사 보고서

대상: `/home/user/leegahuyn/mathlib4/PrimalitySheafVerification/Mock1.lean` (9,831줄, `namespace Mock1`)
선언 통계(`decls_cls.json`, file=Mock1): theorem 655 / def 229 / abbrev 24 / structure 60 / inductive 18 / instance 4 / class 1 / example 3.
theorem 분류: long 206, short_other 227, trivial_tactic 192, short_auto 20, proj_hyp 10. accessor=true인 theorem은 125개(19%).
`#print axioms` 줄은 1,155개(파일의 11.7%)입니다. 같은 이름 목록이 세 군데 섹션에서 되풀이됩니다.
`_from_certificate` 접미사가 붙은 선언은 66개이고, 이 이름은 225번 등장합니다. 대부분 동일한 projection을 이름만 바꿔 복제한 것입니다.

---

## 1. 목적·논문 대응

- 헤더(L1–39)가 밝히는 대상 논문은 Lee Ga Hyun, "Entropy–Growth and Sheaf Stability for Mock Partial Theta and Jacobi Objects"입니다.
- 헤더는 이 논문이 "압도적으로 해석적"이며, 해석적 기계(mock theta, harmonic Maass form, completion/shadow, Rademacher, Kloosterman, Dirichlet twist, p-adic interpolation, entropy–growth 점근)를 **생략(OMITTED)**한다고 정직하게 적고 있습니다.
- 대신 형식화하는 것은 논문에 포함된 "SPT/sheaf-stability 블록"입니다. 구체적으로는 정수 gcd/lcm/CRT, Tor 대용물, 유한 Mahler 보간, 유한 Čech 대용물, S4 유한 행렬, 수치 표의 유리수 재현입니다.
- `PaperClaimId`(L147–160)와 `paperClaimMapEntry`(L221–546)가 주장하는 논문 대응은 다음과 같습니다.
  - Lemma 2(gate/equalizer stability), D4.Eq/D4.Tor, D5.1의 원문 오류와 정정본: **proved**
  - 정정된 Lemma 9(p-adic normalization), Prop I.3(p-adic gluing), Prop I.4(Mahler interpolation), S4/T1/T2(principal-part matrix): **provedViaFiniteProxy**
  - Prop I.5(tail), Thm I.8(base-change stability), T3/T4/T5: **certificateConsumed**
  - 해석적 패키지 전체: **advancedExcluded**
- **라벨 불일치가 있습니다.** 헤더 L29–30은 "Thm I.8 (base-change stability) ↦ thickness_stable_coprime **PROVED**"라고 적습니다. 그러나 claim map(L435–470)은 Thm I.8을 `certificateConsumed`로 분류합니다.
  - 실제 `thickness_stable_coprime`(L3509)은 "c와 서로소인 소수 q에서 gcd의 q-지수가 불변"이라는 한 줄짜리 factorization 사실에 불과합니다.

## 2. 헤드라인 정리 목록

| # | 줄 | Lean 이름 / 진술(요약) | 상태 |
|---|---|---|---|
| 1 | 2615 | `crt_solvable_iff : (∃ x, M ∣ x-a ∧ N ∣ x-b) ↔ (gcd M N : ℤ) ∣ a-b` (Bezout 계수로 증명) | U |
| 2 | 2788 / 2837 | `card_ker_mulLeft` / `torProxy_card : Nat.card (TorProxy M N) = gcd N M` (첫 동형정리와 index 사용) | U |
| 3 | 2843 | `torProxy_equiv_zmod_gcd : TorProxy M N ≃+ ZMod (gcd N M)` (순환군 + 위수) | U |
| 4 | 2914, 2942 | `zmodGcdToTorProxyHom` (생성원 N/gcd를 명시), `zmodGcdEquivTorProxyConstructive` | U |
| 5 | 3302 / 3345 | `torProxyCRTPrimewiseEquiv : TorProxy M N ≃+ Π q∈N.primeFactors, ZMod (q^thickness)` (Mathlib `ZMod.prodEquivPi`, `ZMod.equivPi` 사용) | U |
| 6 | 3047, 3066, 3129 | `gcd_eq_prod_primeFactors`, `card_Tor_eq_exp_IC : gcd = exp(IC)`, `IC_additive_of_coprime_levels` | U |
| 7 | 3597, 3630 | `d51_original_intersection_min_formula_rejected` (PDF D5.1의 min 공식 반박), `D5_intersection_formula_corrected` | U |
| 8 | 7682 | `lemma2_gate_equalizer_stability_under_CRT` (ker = lcm, \|Tor\| = gcd, Tor ≃ ZMod gcd, Tor 자명 ↔ 서로소) | U (위 정리들의 래퍼) |
| 9 | 4824 / 4910 | `finiteMahlerBinomialInversion_constructive`, `finiteMahler_unique_coefficients_constructive` | U, 단 `finiteDifferenceCoeff := A⁻¹·a`로 정의되어 있어 A·A⁻¹ = 1에 불과함 |
| 10 | 5110 / 5174 | `mathlib_mahlerSeries_apply_nat_eq_finiteMahlerEvalSMul`, `MathlibFiniteToInfiniteMahlerBridge.mahlerSeries_interpolates_samples_on_window` | 앞의 것은 U(Mathlib `PadicInt.mahlerSeries_apply_nat` 래퍼), 뒤의 것은 C(필드 `initial_segment`에 조건부) |
| 11 | 7696 | `propI3_padic_gluing_finite_proxy` (lcm 몫에서 쌍별로 같으면 유일한 전역 벡터 존재) | T |
| 12 | 7774 | `propI5_tail_agreement_from_certificate` | C/A (TailCertificate의 필드와 `hsmall_zero`에 의존) |
| 13 | 7803 | `theoremI8_stability_from_certificate` (α 불변 ∧ c_eff 불변 ∧ \|Tor\| 불변) | 앞의 두 conjunct는 **C(순환)**, 셋째는 U(사소함) |
| 14 | 8398 | `S4ActualExtractionMatrix_eq_A_inftyMatrix` | T (정의상 같은 행렬) |
| 15 | 8464 / 8738 | `A_inftyMatrix_rank_eq_D_mathlib`, `S4D6J12Matrix_rank_eq_D6_mathlib` (Mathlib `Matrix.rank`, 오른쪽 역행렬 명시) | U (구체적 유한 행렬) |

## 3. 탈출구·신뢰 기반

- 원문에 `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`는 없습니다. 리드의 사전 확인 결과와 일치합니다.
- 커스텀 `elab`, `macro`, `syntax`, `notation`도 없습니다.
- heartbeat 상향은 없습니다. 옵션 변경은 `set_option maxRecDepth 10000 in` 하나뿐입니다(L933, 문자열 `≠ ""`를 `decide`로 확인하는 곳).
- `#print axioms`는 1,155줄입니다(L3469–3505, 4568–4624, 5440–5505, 5918–5951, 6191–6214, 7224–7293, 7651–7676, 7813–7824, 8085–8095, 8933–9242, 9254–9829).
  - 이 출력은 어디에도 저장되어 있지 않습니다. 파일도 이를 스스로 인정합니다: `elementaryCertificationJudgement.canClaimCompleteNow = false`(L2278), `FormalizationPriorityState.externalAuditRequired`.
- `Classical.choice`/`Classical.choose`가 쓰인 곳은 세 종류이고, 모두 정당한 존재 명제에서 값을 꺼낼 뿐 데이터를 날조하지 않습니다.
  - `vector_glueable_iff_forall_gcd_dvd`(L2717)의 CRT 해 선택
  - `MahlerInverseMatrix` 등(L4676, 4817, 4863)의 `Invertible` 선택
  - `FiniteCover`/Čech(L5529–5794)의 `Nonempty` 기준점 선택
  - 다만 Mahler 쪽에 붙은 "constructive"라는 이름은 오해를 부릅니다. 실제로는 noncomputable이고 Classical.choice를 씁니다.
- `Inhabited`/`default`를 자리표시자로 쓰는 곳은 없습니다. instance는 4개뿐이고(TorProxy의 `AddCommGroup`/`Finite`/`IsAddCyclic`와 `Fintype PaperT5RegressionCertRow`) 모두 정당합니다.
- `decide` 사용은 47곳입니다. 큰 항은 없고 대상은 `Fin 11`/`Fin 12`/`ZMod 25`, `List String` 멤버십, 문자열 비교입니다. 다만 문자열 `decide`(L933–938, L1978–2076)는 커널 비용이 클 수 있습니다.
- **결론:** 형식적 탈출구는 없습니다. 위험은 건전성이 아니라 "무엇이 증명되었는가"라는 의미론 쪽에 있습니다.

## 4. 조건부 인증 감사 (핵심)

조사한 범위: 레포 전체에서 아래 구조체를 구체적으로 인스턴스화하는 정의를 grep했습니다.
- Mock1을 import하는 파일은 `BuildAll.lean`뿐이고, Mock1_Advanced는 `import Mathlib`만 합니다.
- 결과적으로 아래 인증서 대부분은 **레포 어디에서도 인스턴스화되지 않습니다.**

### (a) CIRCULAR: 가정이 결론 그 자체
- **`StabilityCertificate`(L7548–7565) → `theoremI8_stability_from_certificate`(L7803)**
  - 필드 `alpha_invariant : regressionAfter.alpha = regressionBefore.alpha`가 Thm I.8의 결론("α 불변")을 그대로 담고 있습니다.
  - c_eff 불변도 필드 `cardy_alpha_before/after`와 `cardy_normalization_invariant`에서 `rw`만으로 나옵니다.
  - 회귀/Cardy 데이터는 매개변수 `M N c`와 어떤 관계로도 연결되지 않습니다. `M N c`는 `c_ne_zero`와 `coprime_support`에만 등장합니다.
  - 즉 "base change"라는 내용은 진술에 없습니다. 셋째 conjunct(|Tor| 불변)만 실제로 증명되며(`baseChange_obstruction_unchanged_on_coprime_support`, L3527), 이는 gcd에 대한 사소한 사실입니다.
  - 이 인증서의 인스턴스는 0개입니다.
- **`S4PrincipalPartExtractionCertificate.actual_eq_A_inftyMatrix`(L8497)**, **`AInftyMatrixRankCertificate.rank_eq`(L8575)**
  - 결론을 필드로 저장한 "legacy" 레코드입니다.
  - 다만 무조건 버전(`S4ActualExtractionMatrix_eq_A_inftyMatrix`, `A_inftyMatrix_rank_eq_D_mathlib`)이 있으므로 (d) DISCHARGED이기도 합니다.

### (c′) 자유 술어(free-predicate) 인증서: 자명하게 거주 가능하고 실제 대상을 담지 않음
아래 인증서들은 모순은 아니지만, 판정 술어나 대상 자체를 인증서가 스스로 고릅니다. 그래서 내용이 비어 있습니다.

- `TailCertificate.Small : R → Prop`(L5398). `Small := fun _ => True`로 즉시 채워집니다.
- `MahlerPkTubeTailCertificate.reduce : R → ZMod (p^k)`(L5189). `reduce := 0`으로 채우면 "p^k tube"가 자명해집니다.
  - `propI4_tail_higher_coefficients_in_pk_tube`(L7736)의 결론 `InPkTube p k T.reduce …`도 인증서가 고른 `reduce`를 씁니다. Mathlib의 `PadicInt.toZModPow`와 연결되지 않습니다.
- `ModularBookkeepingCertificate.isModular`(L7466), `DifferentialAnalyticCertificate.harmonic`(L7493), `OutsideIdentityCertificate.{outsideRegion,lhs,rhs}`(L7517), `ModularTransportCertificate.shadow`(L7866)
- `BlockFamilyCertificate.assembled*`(L7932–7941): 조립된 값 자체가 자유 필드입니다.
- `ABLinearizationCertificate.pAdicLogLipschitzStatement : Prop` + 증명(L7342–7343): `True`로 채워집니다.
- `FiniteToInfiniteMahlerBridge.tail_control : Prop`(L5050): 증명 없이 Prop만 들고 있습니다.
- `RegressionCertificate.externalRationalCertificate : Prop` + `ols_certificate : NormalEquationsHold ∨ externalRationalCertificate`(L6315–6316): 정규방정식을 우회하는 구멍입니다(아래 참조).
- 파일은 이 경계를 `CertificateBoundaryEntry.doesNotProve`(L1009–1075)에 문서화하고 있어 의도 자체는 정직합니다. 문제는 이름과 PaperClaimMap이 이것들을 각각 "T3/T4/T5", "Prop I.5"에 매핑한다는 점입니다.

### (b) SUBSTANTIVE이지만 사소하게 증명 가능한데 방치됨
- **`RatZModReductionLaws`(L4005)**: 환 준동형 ℤ_(p) → ZMod p^k의 덧셈·곱셈 법칙입니다. 참이고 짧게 증명할 수 있지만 증명도, 인스턴스도 없습니다. `localPadicVector_add_apply`/`mul_apply`(L4035/4044)가 이것에 의존합니다.
- **`TorProxyGluingObstructionCertificate`(L3422)**: `Subsingleton (TorProxy M N) ↔ ∀ a b, Glueable M N a b`입니다. 파일 안의 `torProxy_subsingleton_iff_gcd_eq_one`과 `glueable_iff_gcd_dvd_sub`만으로 증명되지만 방치되어 있습니다.
- **`MathlibFiniteToInfiniteMahlerBridge.initial_segment`(L5135)**: 처음 N+1개의 Mahler 계수가 유한차분 계수와 같다는 필드입니다. Mathlib의 `mahler_coeff`/forward-difference 이론으로 증명할 수 있는 성질인데 가정으로 남아 있습니다. 인스턴스는 0개입니다.

### (d) DISCHARGED: 무조건 대체물이 존재함
- `TorProxyExplicitEquivCertificate`(L3159) → `zmodGcdEquivTorProxyConstructive`(L2942), `zmodGcdToTorProxyHom_one_coe`(L2930)
- `TorProxyCRTDecompositionCertificate`(L3363) → `torProxyCRTPrimewiseEquiv`(L3302). `tor_equiv_primewise_constructive`(L3406)도 같습니다.
- `TorProxyNaturalityCertificate`(L3229) → `torProxyLevelReduction`(L2988), `torProxyLevelReduction_commutes_with_mulLeft`(L3015)
  - 다만 인증서의 `levelMap : ZMod N →+ ZMod N'`은 방향이 반대이고 아무 사상이나 허용합니다. 그래서 대체물과 같은 진술은 아닙니다.
- `FiniteMahlerInterpolationCertificate`(L4718) → `finiteMahlerInterpolationCertificate_of_samples`(L4870)
- `FiniteMahlerInterpolationEngine` → `finiteMahlerInterpolationEngine_constructive`(L4947)
- `PAdicNormalizationFinite` / `PAdicFiniteNormalization` → `padic_normalization_finite_corrected`(L3858), `padic_finite_normalization_corrected`(L4107)
- `D4GateCertificate` → `D4GateCertificate_of_lcm_overlap`(L7411)

### reference/예시 인스턴스: 퇴화 vs 실제 대상
파일에서 실제로 인스턴스화되는 것은 아래 4개뿐이고, 모두 퇴화이거나 동어반복적입니다.

1. **`paperT5RegressionCertificate`(L7043) — 퇴화**
   - 입력은 합성된 2행 `(x=0, y=β̂)`, `(x=1, y=α̂+β̂)`(L7013–7026)입니다. 직선이 이 두 점을 정확히 지나므로 잔차는 0이고, 0 ≤ RSS가 자명하게 성립합니다.
   - `externalRationalCertificate := PaperT5RegressionSummaryRationalized`(L7029)는 "x̂ ∈ [x̂−SE, x̂+SE]"라는 사소한 명제입니다. 이것으로 `ols_certificate := Or.inr …`(L7055)을 채우므로 **정규방정식은 한 번도 검증되지 않습니다.**
   - RSS(제곱합)를 행별 절대잔차 상한으로 쓰는 차원 불일치도 있습니다.
   - docstring(L6998–7001)은 "raw 90행 OLS가 아니다"라고 인정합니다.
2. **`paperT5CardyIntervalCertificate`(L7136) — 동어반복**
   - `factor := ceff/α²`로 정의되어 있으므로 `ceff = factor·α²`는 정의상 참입니다. 모든 구간은 singleton입니다.
   - 유일하게 정보가 있는 진술은 `paperT5_cardyFactor_mem_base_interval`(L7121)의 factor ∈ [0.6, 0.62]입니다. 이 값은 6/π² ≈ 0.6079와 일치하지만, π는 Lean 증명 어디에도 등장하지 않습니다.
3. **`thetaKernelL1TableRow`(L6552) — 표 수치가 서로 연결되지 않음**
   - `residualMeasure`가 `observed`/`prediction`과 연결되지 않은 독립 리터럴입니다. `PaperPredictionTailRow`(L6505)에는 연결 필드가 없습니다.
   - 따라서 "pass"는 리터럴 두 개를 비교하는 것에 불과합니다.
   - 0행은 fail로 정직하게 기록되어 있습니다(L6662).
4. **`s4PDFSelectionAgreement`(L8363) — 정의의 재진술**
   - 모든 필드가 `rfl` 또는 정의의 재진술입니다.

## 5. 정의 충실도

- **`TorProxy M N := ker (mulLeft (M : ZMod N))`(L2814)**: Tor₁^ℤ(ℤ/M, ℤ/N)의 **올바른** 초등 모델입니다(사영분해 0→ℤ→ℤ→ℤ/M에서 나옴). |TorProxy| = gcd와 TorProxy ≃ ZMod gcd가 증명되어 있습니다.
  - Mathlib의 derived Tor와 잇는 다리는 없지만 docstring이 이를 명시합니다(L2807–2813).
  - "Tor₁ := ZMod gcd" 같은 정의상 대용보다는 낫습니다. 핵(kernel)으로 정의하고 기수를 증명했기 때문입니다.
- **`qParam`(L5956)**: Mathlib `UpperHalfPlane` 위의 exp(2πiτ)로 충실하게 정의되었고, |q| < 1이 증명되어 있습니다.
  - 그러나 mock theta, partial theta, Appell–Lerch μ, Jacobi form 같은 **실제 대상은 하나도 정의되지 않습니다.** `CoeffSeries`/`CoefficientChannel`은 함수를 담는 껍데기일 뿐입니다.
- **Mahler**: 유한 부분은 행렬 `choose n j`로 정의되어 충실합니다. Mathlib의 `PadicInt.mahlerSeries`와 잇는 실제 브리지(L5110)도 있습니다.
  - 다만 `finiteDifferenceCoeff`가 역행렬로 정의되어 있어(L4687), 명시적 공식 Δʲa(0) = Σ(−1)^{j−i} C(j,i) a(i)는 증명되지 않습니다.
- **Čech/sheaf (L5507–5951)**: `LocalSection := I → Fin (N+1) → R`, `CechDiff s i j = s i − s j` 수준입니다. "pairwise equal ⇒ 전역 단면"은 동어반복에 가깝습니다. Mathlib의 scheme/sheaf와 잇는 다리는 없으며, 파일 스스로 `planned`로 표시합니다.
- **S4 행렬 (L8099–9006)**
  - `S4ActualExtractionMatrix`는 [I | −I] 패턴으로 **직접 정의**됩니다(L8312–8316).
  - "ridge algorithm" `topDNegativeRowsByRidge := −2N − m2`(L8221)는 PDF 공식을 그대로 옮겨 적은 것이고, 지수 다항식 `E4`에서 도출되지 않습니다.
  - 실제로 `E4 80 50 (−6) = 27,656 > 0`이어서(L8108–8110로 직접 계산), `concreteRows_N80_ell50`는 음수가 아닙니다. E4와 "top-D negative rows"를 잇는 정리는 없습니다.
  - 따라서 `finalReport_s4_extraction_status_certificate_free`(L1207)와 `elementaryCompletionGate_s4_status_closed`(L2254)의 "certificate-free extraction theorem, satisfiedByLean"은 **과장입니다.**
- **회귀/Cardy/tail 표**: 인쇄된 수치를 유리수로 옮긴 것일 뿐, q-series 계수와 연결되지 않습니다.

## 6. 실질 수학 내용

진짜 증명은 모두 학부 수준의 초등 정수론과 유한 선형대수입니다.
- `crt_solvable_iff`(L2615, Bezout)
- `card_ker_mulLeft`(L2788, 첫 동형정리와 index)
- `gcd_eq_prod_primeFactors`(L3047), `card_Tor_eq_exp_IC`(L3066), `IC_eq_zero_iff_coprime`(L3079)
- `gcd_mul_eq_mul_gcd_of_coprime_levels`(L3096). Mathlib의 `Nat.Coprime.gcd_mul`과 중복으로 보입니다(미검증).
- `torProxyCRTPrimewiseEquiv`(L3302)
- `mahlerMatrix_det_eq_one`(L4656)과 보간·유일성(L4824–4920)
- Mathlib Mahler 브리지(L5110, L5150)
- `cardy_ceff_mem_interval_of_rational_bounds`(L6781, 구간 산술)
- `A_inftyMatrix_rank_eq_D_mathlib`(L8464), `S4D6J12Matrix_mulVec_solve`/rank(L8711, L8738)
- `d51_original_intersection_min_formula_rejected`(L3597): PDF 오류를 정직하게 잡아낸 점이 좋습니다.

Mathlib 깊은 결과의 사용은 `ZMod.chineseRemainder`/`prodEquivPi`/`equivPi`, `addEquivOfAddCyclicCardEq`, `Nat.factorization_gcd/lcm`, `PadicInt.mahlerSeries_apply_nat`, `Matrix.det_of_lowerTriangular`, `Matrix.rank`로 얕은 편입니다.

**줄 수 비율(대략)**

| 구분 | 줄 범위 | 비율 |
|---|---|---|
| 레지스트리·상태 장부(String/List-String, ClaimStatus, Priority, Gap, Criterion, PAdicAPIAudit) | L71–2597, L4319–4566 | ≈ 2,850줄, **29%** |
| `#print axioms` | 여러 섹션 | 1,155줄, **12%** |
| 인증서 구조체 + accessor/`_from_certificate` 복제 + 래퍼 | — | ≈ 1,900줄, **19%** |
| 수치 데이터 표(thetaKernel, paperT5, pdfMahler ZMod25, D6J12 항목) | — | ≈ 800줄, **8%** |
| 사소한 정의 펼침·rfl·Čech 동어반복 | — | ≈ 1,000줄, **10%** |
| **실질 수학** (위 목록) | — | ≈ 1,300–1,500줄, **13–15%** |

## 7. 수학적 정확성 / 과장

- Thm I.8의 상태가 헤더(L29–30, "PROVED")와 claim map(`certificateConsumed`) 사이에서 모순됩니다. Lean 진술(L7788)은 α와 c_eff 불변을 **가정**합니다.
- S4 "ridge algorithm extraction"과 "certificate-free"(L475, L1155–1161, L2453) 주장은 정의상 동치 이상이 아닙니다(§5 참조).
- `mahlerMatrix_upper_triangular`(L4643)는 실제로 하삼각입니다. docstring이 이를 인정하지만 이름이 틀렸습니다.
- `S4D6J12SolutionEntry` docstring은 "minimal-norm solution"(L8669)이라고 하지만, 증명된 것은 `mulVec = target`뿐입니다. 최소성은 증명되지 않았습니다.
- `RegressionCertificate.residual_dominated_by_tail`가 RSS를 행별 잔차 상한으로 쓰는 차원 오용이 있습니다(L7056).
- `thetaKernelL1PassingTable_passes`(L6685)는 "예측 오차가 tail bound 이내"처럼 읽히지만, `residualMeasure`가 observed/prediction과 무관한 리터럴이라 그런 의미를 갖지 않습니다.
- `propI3_padic_gluing_finite_proxy`(L7696)는 "p-adic gluing"이라는 이름이지만 p-adic 내용이 없습니다. 몫환 하나에서 "모두 같으면 공통값 존재"라는 사소한 사실입니다.
  - 실질적인 gluing 판정은 `crt_solvable_iff`/`vector_glueable_iff_forall_gcd_dvd`에 있습니다.
- 수학적으로 **틀린** 진술은 발견하지 못했습니다. 문제는 과장과 동어반복입니다.

## 8. 코드 품질

- 9.8k줄 중 약 41%가 레지스트리와 `#print axioms`입니다.
  - 같은 `#print axioms` 목록이 섹션별 감사, `CertificateBoundaryAxiomAudit`, 최종 `AxiomAudit`에 거의 그대로 세 번 반복됩니다.
  - 모든 accessor에 `_from_certificate` 쌍둥이가 붙어 있습니다.
  - `S4_solution_to_D4GateCertificate`, `D4D5_S4_…`, `…_from_certificate`처럼 별칭 체인도 있습니다.
- 문자열 레지스트리(`leanObjects : List String`)는 Lean이 이름의 존재를 검사하지 않습니다.
  - 일부 이름은 실제 선언과 맞지 않습니다(예: L2372–2382 `"claimMap_has_lemma2"`, `"claimMap_has_d4"`, `"claimMap_has_t3t4t5"`, L2518 `"claimMap_advanced_status"`. 실제 이름은 `claimMap_has_lemma2_gate_equalizer_stability` 등입니다).
  - 그런데도 `criterion_paper_claim_map_complete`는 `satisfiedByLean`으로 기록됩니다.
- 장점: CRT/Tor/Mahler 블록의 증명은 짧고 깔끔하며 Mathlib 스타일입니다.
- 업스트림 가치: 낮습니다.
  - `card_ker_mulLeft`("ZMod N에서 M배 사상의 핵의 기수 = gcd")는 PR 후보가 될 수 있지만 Mathlib에 이미 있을 가능성을 확인해야 합니다.
  - `gcd_mul_eq_mul_gcd_of_coprime_levels`는 기존 `Nat.Coprime.gcd_mul`의 재증명으로 보입니다.
- 견고성: heartbeat 상향은 없습니다. `decide`(문자열·`Fin 11` injective·`ZMod 25` 평가)는 비용 면에서 다소 민감합니다.

## 9. 컴파일 위험

- `build-logs/pr9-final-branch-health.txt`의 stage 표에는 Mock2/Advanced/FunctionalAnalysis만 있고 **Mock1 항목은 없습니다.**
  - Mock1을 언급하는 것은 `build-evidence/continuation/FA_QYM_13FILES_15CHECK_PIPELINE_CONTRACT_20260814.md`의 필수 파일 목록뿐입니다.
  - **Mock1의 컴파일 성공 또는 실패를 보여주는 직접 로그는 찾지 못했습니다.**
- 파일 스스로도 빌드 로그를 "external evidence required"로 표시합니다(L2181, L2359).
- 이 파일을 import하는 곳은 `BuildAll.lean`뿐입니다.
- 의심 지점(추정이며 미검증):
  - 구조체 필드의 `Type*`(L4302–4303 `PadicIntReductionBridge`): 우주 매개변수 처리
  - 문자열 `decide`(L933–938, L1978–2076)의 커널 비용
  - `IsBoundedSMul` 등 Mathlib 이름의 변동(L5112)
  - `fin_cases … <;> exact …`(L6688)
- 명백한 문법 오류나 존재하지 않는 API 사용은 읽는 동안 발견하지 못했습니다. 판단은 리드의 로컬 빌드에 맡깁니다.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | **8** | 탈출구 0, Classical 사용은 정당. 다만 Mock1 단독 빌드 증거가 없음 |
| 조건부 인증의 정직성(비순환성) | **5** | `doesNotProve` 경계 표와 `canClaimCompleteNow=false`는 정직함. 그러나 Thm I.8은 순환적이고 헤더는 "PROVED"로 표기, S4 "certificate-free"는 과장, 자유 술어 인증서와 퇴화 회귀 인스턴스가 있음 |
| 수학적 실질성 | **3** | gcd/lcm/CRT/factorization과 단위삼각행렬·소형 구체 행렬 수준. 제목의 mock theta·Jacobi 내용은 0 |
| 정의 충실도 | **5** | TorProxy, qParam, Mathlib Mahler 브리지는 충실함. S4 추출, 회귀·tail 표, Čech는 정의상 자명하거나 연결이 끊김 |
| 코드 품질·유지보수성 | **3** | 약 41%가 레지스트리와 `#print axioms`이고, 3중 복제와 문자열 이름 불일치가 있음. 핵심 증명 자체는 깔끔함 |
| **종합** | **4** | 정직하게 범위를 좁힌 초등 CRT/Tor 코어는 견실함. 그러나 파일의 대부분은 장부이고, "certificate-consumed" 정리들은 내용이 없거나 순환적임 |

**가장 중요한 단서:** Mock1이 실제로 증명하는 것은 "gcd/lcm/CRT와 ZMod 핵의 기수" 수준의 초등 사실과 유한 행렬 계산뿐입니다. 논문의 해석적·모듈러 주장(Thm I.8의 α/c_eff 불변, Prop I.5 tail, T3–T5)은 결론을 필드로 담거나 판정 술어를 스스로 고르는 인증서로만 등장하며, 그런 인증서의 인스턴스는 레포 어디에도 없습니다(유일한 회귀/Cardy 인스턴스는 퇴화). "conditional certification"이라는 표현이 이 부분에서는 실질 내용을 갖지 않습니다.

---

## Coverage log
- L1–1000: Read(헤더, import, `AdvancedExcludedTopicList`, `PaperClaimStatus`/`PaperClaimId`/`paperClaimMapEntry`/`PaperClaimInventory`, CertificateBoundary 시작)
- L1000–2099: Read(CertificateBoundary, `finalCertificationReport`, FormalizationPriority, FinalPriority, MathlibGap, CertificationCriterionStatus)
- L2100–3098: Read(ElementaryCompletionGate, CertificationCriterion, §A–§C CRT/Tor, TorProxy, level reduction, §D thickness/IC)
- L3099–3998: Read(`gcd_mul…`, IC additive, TorProxy 인증서, primewise CRT, Gluing 인증서, 감사 섹션, I.8 thickness, §E D5.1, §F Lemma 9, p-adic reduction)
- L3999–4898: Read(RatZModReductionLaws, finite normalization, unit recovery, PadicIntReductionBridge, PAdicAPIAudit 표, Mahler 행렬·보간)
- L4898–5797: Read(Mahler 유일성·engine, Mathlib Mahler 브리지, pk-tube, ZMod25 예시, TailCertificate, Čech 대용물)
- L5798–6647: Read(Čech obstruction, qParam, CoeffSeries/Channel, Discriminant, GrowthFitData, TailRow, Regression, RatInterval, scientificRat, thetaKernel 표 0–10행)
- L6648–7446: Read(thetaKernel 11행, passing table, Cardy convention·interval, paperT5 rationalization·인증서 인스턴스, CardyCertificate, ABLinearization, D4)
- L7447–8245: Read(D4 projections, Modular/Differential/Outside 인증서, StabilityCertificate, 논문 래퍼, MultiplierSystem, ModularTransport, BlockFamily, S4 E4/ridge)
- L8246–9044: Read(S4 SelectedRows, A∞, PDF agreement, rank, legacy 인증서, D6J12, S4→D4 브리지, S4/Priority 감사 섹션)
- L9045–9831: Read(MathlibGap/Criterion/ClaimMap/CertificateBoundary `#print axioms`, Examples, 최종 AxiomAudit). 이 구간은 `#print axioms` 목록이라 훑어 읽었습니다(skim).
- 보조 작업: `decls_cls.json` 집계(python), escape-hatch·Classical·decide grep, 레포 전체 인증서 인스턴스화 grep, `build-logs`/`build-evidence`의 Mock1 언급 grep
