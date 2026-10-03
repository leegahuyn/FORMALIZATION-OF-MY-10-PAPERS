# Spt1 감사 보고서 — `PrimalitySheafVerification/Spt1.lean` (8,087행)

대상: Lee Ga Hyun, "A Primality Sheaf and Global Certification" (Spt 1). `import Mathlib` 단독.
구성: PART A `Spt1`(1–1288) / PART B `Spt1SheafFull`(1294–3333) / PART C `Spt1IntrinsicSheaf`(3345–3432) / PART D(3457–3564) / PART E(3581–8087; `Spt1CechGeometry`, `Spt1CechArithmetic`, `Spt1DerivedTor`, `Spt1ModularCRT`, `PadicLog`, `PrincipalOpenCech` 포함).
통계(decls JSON): theorem 535 + lemma 2, def 216, abbrev 60, structure 35, class 3, instance 3, inductive 2, example 12. 접근자 투영 증명 15, `rfl`/`Iff.rfl` 증명 33, 항(term) 한 줄짜리 재수출/투영 약 156개 → 정리의 약 35%가 한 줄 래퍼.

---

## 1. 목적·논문 대응

- 헤더(1–36): "A Primality Sheaf and Global Certification". 산술 코어(공통 잉여 섬유 `gcd(M,p^k)`, 국소 두께 `ε_p = min(v_p M, k)`, 지표 복잡도 IC, 등화자 지지), Spec ℤ 위 주열린집합 기저 `D_f`, 네 개의 검출 층 `F_num/F_mod/F_padic/F_EC`의 섬유곱 `F`, 정리 1(전역 단면 ⇔ 소수), Lucas/Pocklington 인증서.
- 주장하는 논문 항목: Lemma 2.3, 2.6, 2.10, Prop 2.4(a)(b), 2.5, Thm 2.1(i), Rmk 2.2/2.7/2.8, Cor 2.9/2.12, Def 2.11/4.11/4.13, Thm 4.1, Cor 4.2, Lemma 4.3, Prop 4.4, Lemma 4.6, Prop 4.7/4.9, Thm 4.12, Lemma 4.14, Prop 4.16, Cor 4.17, Prop 4.18, Thm 4.20, Cor 4.21, Thm 5.1, Prop 5.4, Lemma 6.1, Thm 6.2, Lemma 7.3, Cor 7.4, Prop 7.5/7.7/7.9/7.10, Cor 7.8/7.11, Eq.(2)(4)(5)(7)(10), 논문 "Lemma A/B/C/5/6/15/16, Prop 2/7/17, Thm 1/14/18". PART E 헤더(3567–3579)는 "COMPLETE paper coverage"를 주장.
- 파일 스스로 정정(CORRECTED)으로 보고하는 항목: Thm 6.2 극소성(minimality)은 진술대로는 거짓(2224–2239), 국소화 줄기(stalk) 교집합=두께 등식은 거짓(4957–5106), L2 gcd→min/lcm→max(97).

## 2. 헤드라인 정리 목록

| # | 행 | 이름 | 진술(요약) | 상태 |
|---|---|---|---|---|
| 1 | 147 | `card_ker_mulLeft` | `Nat.card (mulLeft (M:ZMod N)).ker = gcd N M` | U (진짜 증명: 상/핵 지수 계산) |
| 2 | 5723 | `Spt1DerivedTor.tor1_obj_iso` | `(Tor (ℤ/M) 1).obj (ℤ/N) ≅ ModuleCat.of ℤ (ZMod (gcd M N))`, `Tor := Functor.leftDerived (tensorLeft N)` | U (명시적 사영 분해 `resP`(5650)를 통한 진짜 유도함자 계산 — 파일 최고의 성과) |
| 3 | 5768 / 6158 | `torOne_zmod_card_eq_gcd_uncond`, `torOne_crt_directSum_addEquiv_unconditional` | 진짜 Tor₁의 위수 = gcd; `Tor₁ ≃+ ⊕_q ZMod(q^min(v_q M,v_q N))` | U |
| 4 | 6183 | `obstructionFree_iff_genuine_torOne_subsingleton` | `obstructionFree M p k ↔ Subsingleton (Tor₁(ℤ/M, ℤ/p^k))` | U (프록시↔진짜 Tor 다리) |
| 5 | 224 / 1107 / 1081 | `card_Tor_eq_exp_IC`, `IC_le_log`, `IC_add_coprime` | `gcd M N = exp(IC M N)`, `IC ≤ log N`, 서로소 가법성 | U |
| 6 | 1884 | `theorem1_fourLayer` | `X.Prime ↔ Nonempty (globalSections E X)` (2 ≤ X) | U이나 사실상 T: `prime_iff_all_primeDvd`의 포장 |
| 7 | 8022 | `globalSectionsData_nonempty_iff_prime_with_parameters` | 매개변수 부대조건(`k ≤ X.factorization q`, `r∣X → r∤Δ`) 하에 `Nonempty Γ(F_data) ↔ X.Prime` | U (부대조건 때문에 소수 X에서 p-adic 층은 k=0 또는 q=X,k≤1에서만 만족 가능) |
| 8 | 7959 | `globalSectionsData_sound_primality_via_equalizer_padic` | `EqualizerPadicSoundnessProfile` 하에 소수성 | C — 가정이 순환(§4 참조) |
| 9 | 2264 / 2276 | `VisiblePrimesProfile.Valid.sound`, `LucasCertificate.sound` | Lucas 조건 ⇒ 소수 | U (Mathlib `lucas_primality` 직접 사용) |
| 10 | 1263 | `minimalCertificate_sound` | `X < pn²` + `htrial`(pn 미만 소수로 나누어지지 않음) ⇒ 소수 | C/U — 실질은 `htrial`(시행나눗셈) 자체; 구조체 필드 `A, M, k, hcop, hA` 미사용 |
| 11 | 3238 | `theorem1_via_GK_step` | `GoldwasserKilianPropagationTheorem E` + ECPP 단계 ⇒ 소수 | C — 가정이 거짓/공허(§4) |
| 12 | 7351 | `PadicLog.eq4_padic_congr` | `(Hk)` ⇒ `‖log(1+u) − u‖ ≤ p^{-k}` (진짜 ℚ_[p] 로그, `u = uexp …`) | C — 문서는 "UNCONDITIONAL"이나 `[PadicLogTailCertificate p]`에 의존(§3,§4) |
| 13 | 6953 / 7066 | `padicLogSeries_summable`, `padicLog1p_norm_le_self` | ‖x‖<1에서 급수 합가능, `‖log(1+x)‖ ≤ ‖x‖` | U |
| 14 | 4933 / 5020 | `failure_stalk_sum_eq_thickness`, `localizedFailureStalkThickness_unfillable` | `(M)ℤ_P ⊔ (p^k)ℤ_P = (p^ε)ℤ_P`; 교집합판 인증서는 M=p,k=2에서 채울 수 없음 | U (진짜 국소화 계산, 정정 포함) |
| 15 | 2233 / 2201 | `headline_thm6_2_minimality_correction`, `fnum_partial_infinite_composites` | 완전 게이트에서는 EC-only 반례 없음 + 부분 필터(시행나눗셈/Fermat) 쌍별 독립(49, 341, 561, 91), 합성 통과자 무한 | U (`decide` 기반 증인) |
| 16 | 2523 / 2867 / 2933 | `weak_hasse`, `ECFiniteFibreModelFor.ofEllipticModel`, `ECReducedModelLink.model_Δ_ne_zero` | `a_q² ≤ q²`; Mathlib 타원곡선 군법칙을 `Option AffinePoint`로 이송; 변수변환 링크로 Δ≠0 유도 | U |
| 17 | 3936 / 3949 | `thm2_1_MtA_linearization`, `thm2_1_truncLog_linearization` | `(Hk)` + `MtALogInput` ⇒ `u ∈ p^kℤ_p` ∧ `k ≤ v_p(Λ−u)` | 첫 연언은 U(`Hk_imp_phiSum_val`), 둘째 연언은 가정 그대로(T) |
| 18 | 4203 | `prop2_5_uniform_design_exists_Hk` | `Prop25UniformDesignAssembly` ⇒ `∃ m y, Hk p M A m q k Y` | C — `y`는 `Hk`에 등장하지 않는 유령 변수 |
| 19 | 7880 | `theorem6_2_sheaf_objectwise_terminal` | 4-투영 콘의 유일 인수분해 | U이나 자명(콘 필드가 같은 기저 함수를 강제) |

## 3. 탈출구 / 신뢰 기반

- 주석·문자열 제거본(`Spt1.code.lean`) 기준: `sorry/admit/axiom/native_decide/opaque/unsafe/implemented_by/elab/macro/syntax` 0건. `#print axioms` **0건** — 15개 가량의 `section AxiomAudit…`(1285, 2241, 2949, 3327–3331, 3429, 3513, 3561, 5108, 6164, 6168, 6192, 7369, 8084)은 모두 **빈 섹션 또는 주석뿐**. "감사" 표기가 실제 검증 명령 없이 존재함.
- 옵션: `maxHeartbeats 800000 in` 2개(5573 `resC_proj`, 5589 `mulN_mono`), `maxRecDepth 4000/8000 in` 5개(2078, 2107, 2114, 2120, 2161 — `decide`로 `(2:ZMod 341)^340=1`, `(2:ZMod 561)^560=1`, `¬Nat.Prime 561` 등 커널 계산), `maxSynthPendingDepth 16`(6928, `in` 없이 `PadicLog` 네임스페이스 끝까지 유효), 린터 7종 전역 비활성(42–48).
- 최근 커밋 `e52217bf`("batch-fix Spt1 forbidden proof"): 865행 예제의 `native_decide`를 `card_ker_mulLeft`를 쓰는 진짜 증명으로 교체(+4/−1). 정당한 수정. 단 3348–3350행 docstring은 아직 "the `native_decide` witnesses below"를 언급(낡은 주석).
- **숨은 가정(타입클래스)**: `class PadicLogTailCertificate`(7083)를 `variable [PadicLogTailCertificate p]`(7088)로 선언. 파일 어디에도 instance가 없음(grep 확인). 7091 `padicLog1p_sub_trunc` 이후 `padicLog1p_sub_self_norm_le`(7187), `padicLog1p_congr_self_of_pow`(7194), `padicLog1p_add_congr`(7272), `padicLog1p_starPow_congr`(7296), `logY_eq_pn_logA_mod`(7320), `padic_congr_of_boundOrZero`(7341), `eq4_padic_congr`(7351), `eq4_padic_congr_discharges_without_additivity`(7361) 모두 이 클래스에 의존하면서 docstring은 "UNCONDITIONAL / NO hypothesis"라고 표기. 내용은 참(`Summable.sum_add_tsum_nat_add`로 한두 줄에 증명 가능)이므로 건전성 문제는 아니나 **라벨이 틀림**. `PadicLogTendstoCertificate`(6969), `PadicLogNonarchSummabilityCertificate`(7158)도 같은 형태(주 사슬엔 미사용).
- `Inhabited`/`default`/`Classical.choice`로 데이터를 날조하는 패턴 없음. `glue`(4429)의 `Classical.choose`는 정당. `deriving Inhabited`(1414, 4490)는 무해.

## 4. 조건부 인증 감사 (핵심)

| 가정/인터페이스 | 위치 | 분류 | 근거 |
|---|---|---|---|
| `GoldwasserKilianPropagationTheorem E` | 3082 | **(c) 거짓/공허** | `ECRegularityCertificate E X`(2623)·`ECStepCertificate E X`(2977)의 어떤 필드도 `X`를 언급하지 않음(**X는 유령 인덱스**). ECPP 계산이 후보 `ℤ/X`가 아니라 임의의 알려진 소수 `q` 위 모델에서 이루어지고, GK 하한도 `X`가 아닌 `count.q`로 표현(2969). 따라서 하나의 단계 인증서가 모든 X에 재사용 가능. 구체 예: E: y²=x³−x(Δ=64), q=7(양호 환원), 모형 y²=x³+3 over F₇은 13점(소수, 13 > (7^{1/4}+1)²≈6.9), cofactor=1, P≠0 → 인증서 존재, `ECPPChain E 13`은 `prime` 생성자로 존재 ⇒ hGK는 `Nat.Prime 4`를 함의 ⇒ **거짓**(Lean으로 구성하진 않았으나 논증 수준에서 명확; 점 개수는 Python으로 확인). Δ_E=0이면 양호환원 소수가 없어 인증서가 공집합 ⇒ 가정은 공허하게 참이고 사슬은 `prime h` 뿐. 어느 경우든 `ECPPChain.sound`(3105), `theorem1_via_GK_step`(3238)은 내용 없음. |
| `EqualizerPadicSoundnessProfile` | 7932 | **(a) 순환** | 필드 `unitGate : SmallPrimeExcludedByUnitGate X`(7915: "ℓ 소수, ℓ∣X, ℓ²≤X ⇒ False")는 X≥2에서 **그 자체로 X.Prime과 동치**(합성수면 minFac²≤X). 증명(7959)에서 p-adic/Čech 분기는 합성수에선 절대 도달하지 않는 죽은 분기. 게다가 `FDataPadicCechObstruction`(7665)의 `nonzeroEqualizerClass` 필드는 전역 단면을 제한한 가족에 대해 항상 거짓(`FDataGluesTo_forces_equalizerClass` 7640)이므로 `ProperPrimeFDataObstruction`(7726)은 사실상 공집합. 문서의 "숨은 시행나눗셈을 대체"(7926–7931)는 반대로 시행나눗셈을 가정에 넣은 것. 또한 같은 결론은 가정 없이 `globalSectionsData_sound_primality`(7903)로 이미 증명됨. |
| `liftBaseToData` | 7980 | (a)에 가까움 | `theorem1_fourLayer_sound_via_equalizer_padic`은 위 순환 프로파일 + 임의 함수 가정. |
| `[PadicLogTailCertificate p]` | 7083/7088 | (b) 참이나 미방전, **"UNCONDITIONAL" 오표기** | §3 참조. 쉽게 (d)로 만들 수 있었음. |
| `MtALogInput p k Λ u` | 3912 | **(a) 순환** | 정의가 `k ≤ v_p(Λ−u)`이고 `thm2_1_MtA_linearization`(3936)의 둘째 결론이 바로 그것. `rmk2_2_uniform_remainder`(3980), `MtALogInput_of_truncLog_bound`(3928), `eq4_congruence`(6867), `thm2_1_truncLog_linearization`(3949, `htrunc`=결론)도 동일. |
| `PadicLogAPI p` | 3858 | (c)-퇴화 | `log : ℚ → ℚ`; `log := id`로 자명하게 만족 가능(`truncLogApproxRat_sub_self_boundOrZero`가 이미 증명). 파일도 6921–6923에서 "degenerately witnessed"라고 인정. 이 API에 조건부인 `thm2_1_padicLog_linearization_of_API`(3892), `eq4_via_API`(6892)는 진짜 로그에 대해 아무 정보 없음. 진짜 로그는 `PadicLog.padicLog1p`(6961)로 따로 구현됨. |
| `PadicLogAdditive` | 7211 | (b) | 진짜 깊은 정리(정확한 가법성). 파일은 비필수로 명시. `padicLog1p_starPow`(7217), `logY_eq_pn_logA`(7232)만 의존. |
| `Hk p M A m n k Y` | 460 | (b) | 논문 자체의 설계 가설 (Hk). 정당. 단 `Hk_of_phiTerm_certificates`(794)는 가정=결론(T). |
| `UniformDesignBounds` | 807 | (b) | 만족 가능(예: M=p^σ). `prop2_5_uniform_design_Hk`(4108)는 진짜 linarith 조립. |
| `Prop25UniformDesignAssembly` | 4150 | (b)이나 약화 | `bounds_of_crt`가 `UniformDesignBounds`를 그대로 반환해야 하며, 결론 `∃ m y, Hk …`에서 `y`는 무관(Hk가 y에 의존하지 않음). CRT 단계는 장식. |
| `SatisfiesHasse` | 2370 | (b) | 참인 깊은 정리(Mathlib 부재). `ec_hasse`(2378)는 가정=결론(정직하게 interface로 표기). |
| `KerMulLeftCyclicCertificate` 등 | 262–363 | (d) | `kerMulLeft_isAddCyclic`(374, `inferInstance`)로 방전. |
| `TorKernelComparison` | 5488 | (d) | `torKernelComparison_genuine`(5754)으로 방전. |
| `LocalPrimePowerKernelCyclicityAvailable` | 6072 | (d) | `localPrimePowerKernelCyclicityAvailable_proved`(6140). |
| `ECFiniteFibreModelFor` | 2794 | (d) | `ofEllipticModel`(2867) / `ECReducedModelLink.available_finite_model`(2944). |
| `LocalizedFailureStalkThicknessCertificate` | 4857 | **(c) 공허(파일이 직접 증명)** | `localizedFailureStalkThickness_unfillable`(5020). 그런데 이에 의존하는 `prop4_9_failure_stalk_thickness_localized`(4867)는 여전히 정리로 남아 있음(공허). 정직하게 정정되어 있으나 제거되진 않음. |
| `SpfPadicBaseChangeInterface` | 5284 | (c)-자명 | 유일한 "명제" 필드가 `completedFailureKernel M k = completedFailureKernel M k`(rfl). `SpfZp := Unit` 등으로 즉시 거주. 헤더(34)는 "[INTERFACE] Formal Spf(ℤ_p) base-change"로 광고하지만 내용 0. |
| `PrincipalOpenGluingCertificate` | 7537 | (b) 참이나 미방전 | 술어가 점별이므로 일반 `cech_equalizer_gluing`(4452)에서 쉽게 증명 가능. 헤더(32–33)는 이를 "[CERTIFIED]"로 표기. 의존 정리: `item7_F_data_principalOpen_topCover_from_gluingCertificate`(7739), `item7_F_principalOpen_topCover_from_gluingCertificate`(7775). |
| `ECRegularityCertificate`의 `groupOrder • P = 0` 필드 | 2981 | 자명 | 유한군에서 Lagrange로 항상 참. |

참조/예시 인스턴스: Mock1_Advanced식 "영(0) 인스턴스"는 없음. 대신 `baseDatum := {residue:=0, modulus:=1, threshold:=0, discriminant:=1}`(1436)이 모든 원래 층 `F_num…F`의 단면을 강제하는 고정값 — 층 `F`의 단면 집합은 각 열린집합에서 부분단일집합(subsingleton)이 되어 층 구조는 술어 `∀p, gate p`를 포장한 것에 불과(`layer_nonempty_iff` 1890). 비중복성 증인(1691–1773)은 파일 스스로 "payload/bookkeeping non-redundancy, not primality-filter"라고 명시(1662–1665, 1850–1863). `Spt1IntrinsicSheaf`(3345–3432)의 비중복성 증인은 서로 다른 매개변수(모듈러스·탐침)를 비교하는 장난감 수준.

## 5. 정의 충실도

- **Tor₁**: 처음엔 `(mulLeft (M:ZMod N)).ker` 프록시였으나, `Spt1DerivedTor.Tor := Functor.leftDerived (tensorLeft N)`(5351)의 진짜 유도함자와 `tor1_obj_iso`로 연결됨 → **충실, 다리 존재**. 매우 좋음.
- **층/Spec ℤ**: `TopCat.of (PrimeSpectrum ℤ)`, `TopCat.subsheafToTypes`, `PrimeSpectrum.basicOpen` 등 Mathlib 진짜 객체 사용. 그러나 "소수성 층"은 섬유가 `baseDatum`으로 고정된 술어 부분층이고, 정리 1은 산술 동치 `prime_iff_all_primeDvd`(1300)의 재포장. 기하학적 내용은 장식적. `F_EC`의 "타원곡선 층"은 `q ∤ Δ_E` 조건뿐이며 `gateNum`에 함의됨(1393).
- **EC/ECPP**: 단축 Weierstrass 모형·점 개수·Mathlib 군법칙 이송은 충실. 하지만 ECPP 인증서가 후보 X와 무관한 체 `F_q` 위에서 정의되어 **실제 ECPP(ℤ/Xℤ 위 곡선)와 다른 대상**. `ECPointCountCertificate.model`은 `E`와 무관한 자유 모형(2541; `ECReducedModelLink`로 선택적 연결).
- **p-adic 로그**: `PadicLog.padicLog1p`(6961)는 ℚ_[p] 위 진짜 `tsum` — 충실. 반면 `PadicLogAPI`/`MtALogInput`은 프록시이며 퇴화 만족 가능.
- **Spf(ℤ_p)**: 실질 없는 인터페이스. `Spec(ℤ_p) → Spec ℤ` comap(5234)는 진짜이나 얕음.
- **X = F_n(A)S_n(A)**: 논문에 정의가 없다며 `Xexp := Y + canonExpTail`(6775)로 **정의**하여 Eq.(2)를 정의적으로 성립시킴(`canonical_expansion` 6785, `phiSum_eq_uexp` 6840은 환 항등식). 파일이 정직하게 설명하나, "Gap A 폐쇄"는 재구성일 뿐.
- **IC, localThickness, commonResidueIndex**: 단순 정의, 충실.

## 6. 실질 수학 내용

진짜 증명(비자명 논증, Mathlib 심층 사용):
- `card_ker_mulLeft`(147), `gcd_eq_prod_primeFactors`(207), `card_Tor_eq_exp_IC`(224), `IC_add_coprime`(1081), `IC_le_log`(1107), `gcd_mul_coprime`(987), `padicDigit_reconstruction`(1139), `global_certificate_coprime`(1228), `minimalCertificate_sound`(1263).
- p-adic 평가: `truncLogTermInt_valuation_ge`(649), `truncLogTermRat_valuation_ge_of_ne_zero`(687), `padic_log_term_survives`(631), `padicValRat_sum_ge`(3597), `Hk_imp_phiSum_val`(3627), `hk_certification_split`(3998), `prop2_4a_exact_order_factorization_nat`(4278).
- 유도 Tor: `resP`(5650; quasiIso 증명), `resC_exactAt_succ`(5596), `kerLTensor_equiv_gcd`(5686), `tor1_obj_iso`(5723), `kerMulLeftPiAddEquiv`(5943).
- 국소화: `algebraMap_p_not_mem_localized_p2`(4969), `kernel_ne_fibre_of_ne`(5060), `failure_stalk_sum_eq_thickness`(4933).
- EC: `sq_fiber_card_le_two`(2468), `affine_card_le`(2491), `weak_hasse`(2523), `projectivePointEquivPoint`(2433), `reductionMod_Δ_ne_zero`(2906), `ECReducedModelLink.model_Δ_ne_zero`(2933), `largePrime_dvd_addOrderOf`(3033).
- p-adic 로그: `padicLogSeries_summable`(6953), `padicLogSeries_norm_le_self`(7025), `padicLog1p_norm_le_self`(7066), `padicLogSeries_tendsto_zero_pk`(7142), `padicLog1p_add_congr`(7272), `padicLog1p_starPow_congr`(7296).
- 기타: `fnum_partial_infinite_composites`(2201), `cech_equalizer_gluing`(4452).

대략적 비율(행 기준, 추정): 진짜 수학(위 증명 + 필요한 정의) **약 30–35% (~2,500–2,800행)**; 나머지 65–70%는 docstring/주석, 재수출 별칭(PART D/E의 논문 번호 래퍼, 6174–6370 등), 게이트/페이로드 래퍼, `Spt1ModularCRT`(6377–6653)의 `rfl` 래퍼, 가용성 마커(`…Available`), 인증서 구조체와 접근자, 순환 프로파일. 정리 537개 중 약 190개(≈35%)가 한 줄 재수출/`rfl`/투영.

## 7. 수학적 정확성 / 과대 주장

- **"UNCONDITIONAL" 오표기**: `eq4_padic_congr`(7351), `padicLog1p_sub_trunc`(7091, docstring "Truncation error = tail (UNCONDITIONAL)") 등 — 실제로는 `[PadicLogTailCertificate p]` 의존.
- **GK/ECPP 층**: §4의 유령 X 문제로, "recursive ECPP chain"은 수학적으로 잘못 모델링됨. docstring(2618–2622, 3078–3081)은 정상적 ECPP처럼 서술.
- **E3 건전성 경로**(7926–7970): "p-adic/Čech 등화자 경로로 건전성"이라 주장하지만 실제로는 시행나눗셈 필드(`unitGate`)가 전부.
- **"COMPLETE paper coverage"**(3567–3579): 많은 항목이 재수출/동어반복 또는 공허 인증서(`prop4_9_failure_stalk_thickness_localized`)로 "덮여" 있음.
- **낡은/모순 docstring**: 234–237, 252–258, 313–330, 5311–5315는 "Mathlib에 부분군 순환성 인스턴스가 없다"고 하나 374행에서 `inferInstance`로 해결됨. 3348–3350의 `native_decide` 언급 낡음. 헤더 31–33의 [CERTIFIED]/[INTERFACE] 목록은 이후 방전된 항목과 불일치.
- **극소성 정정**(2224–2239) 및 **줄기 교집합 정정**(5098–5106)은 수학적으로 올바르고 정직한 정정 — 칭찬할 부분.
- `prop7_9_obstruction_eq_after_dropping`(8069), `obstructionIndexAfterDropping`(8057)은 drop 인자를 무시하도록 정의된 자명 진술.
- `ec_card`(2361)는 `frobeniusTrace`의 정의를 되푸는 항등식.

## 8. 코드 품질

- 8,087행 단일 파일, 5개 PART와 네임스페이스 재진입(`Spt1`/`Spt1SheafFull` 두 번씩) — 조직이 산만. `VisiblePrimesProfile` 이중 정의(874, 2246), `global_certificate_iff`(1218)=`prime_iff_all_primeDvd`(1300), `kerMulLeft_primePow_card_eq_localThickness`(411)=`tor_primePow_card_eq_localThickness`(419) 등 중복. 린터 7종 전역 비활성.
- 동일한 p-adic 로그 코드가 Spt3(4267, 4311)·Spt4(5354)에도 복제됨(grep 확인) — 모듈 간 중복.
- 빈 `AxiomAudit` 섹션 다수(신뢰감 연출용으로 보임).
- Mathlib 상류 후보: `card_ker_mulLeft`(ZMod 곱셈 핵의 위수), `tor1_obj_iso`(Tor₁(ℤ/M,ℤ/N) ≅ ℤ/gcd — Mathlib에 없을 가능성 높음, 가치 큼), `sq_fiber_card_le_two`/`affine_card_le`(#E(F_q) ≤ 2q+1), `padicValRat_sum_ge`, p-adic 로그 기본(`padicLog1p` 합가능성·노름 상계, 단 Mathlib 기존 API와 조율 필요).

## 9. 컴파일 위험

- `build-logs/`, `build-evidence/`, `evidence/`에 Spt1 전용 컴파일 로그 없음(`FA_QYM_13FILES…md` 91행에 대상 파일로 나열될 뿐). 현재 HEAD 컴파일 여부는 미확인(리드가 별도 확인 중).
- 위험 요소: (i) `decide`로 `(2:ZMod 561)^560 = 1`, `¬Nat.Prime 561` 등 커널 계산(2081–2173, maxRecDepth 8000) — 시간/깊이 위험 중간. (ii) 6967, 7081 docstring이 "Lean 4.30"을 언급하는데 고정 툴체인은 v4.33.0-rc1 — 버전 이동 흔적. (iii) `maxSynthPendingDepth 16` 전역 설정. (iv) `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`(7067, 7098)는 Mathlib 소스에 문자 그대로는 없지만 `Ultra.lean:347`의 `norm_tprod_le_of_forall_le_of_nonneg`에서 `to_additive`로 생성되는 것으로 보임(위험 낮음). (v) `variable [PadicLogTailCertificate p]`가 이를 쓰지 않는 정리들에도 자동 포함되어 `unusedSectionVars` 경고 가능(오류는 아님).
- 주요 Mathlib 이름들(`isoLeftDerivedObj`, `moduleCatCyclesIso`, `addEquivOfAddCyclicCardEq`, `lucas_primality`, `pointEquiv`, `variableChange_Δ`, `ZMod.equivPi`, `quasiIsoAt₀_iff` 등)은 고정 Mathlib 트리에 존재함을 grep으로 확인.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 8 | sorry/axiom/native_decide 0, heartbeat 상향 2곳뿐; 감점: 미제공 타입클래스 가정이 `variable`로 숨어 있고 `#print axioms` 없음, 컴파일 미확인 |
| 조건부 인증의 정직성(비순환성) | 5 | 스스로 거짓 인증서·붕괴를 증명해 정정한 점은 모범적이나, GK 가정은 유령 X로 거짓, E3 프로파일은 순환, `MtALogInput`=결론, "UNCONDITIONAL" 오표기 |
| 수학적 실질성 | 6 | 진짜 유도함자 Tor₁ 계산, ℚ_[p] 로그, IC 항등식, 약한 Hasse 등 실질 있음; 헤드라인 "소수성 층" 정리는 산술 동치의 포장 |
| 정의 충실도 | 6 | Tor·Spec ℤ·Weierstrass·ℚ_[p] 로그는 Mathlib 실객체(다리 존재); ECPP는 잘못된 대상, Spf는 빈 인터페이스, `Xexp`는 정의로 맞춘 재구성 |
| 코드 품질·유지보수성 | 5 | 8k행 단일 파일, 중복·재수출 과다(≈35%), 낡은 docstring, 빈 감사 섹션, 린터 비활성; 일부 상류 가치 있는 보조정리 |
| 종합 | 6 | 실질적 핵심(Tor, p-adic)은 견실하나, 주변부 인증 구조 일부가 공허·순환이며 라벨이 과장됨 |

---

## 커버리지 로그

원본 `.lean` 순차 정독(건너뛴 범위 없음):
1–1000, 1000–2000, 2000–3000, 3000–4000, 4000–5000, 5000–6000, 6000–6900, 6900–7549, 7549–8087(파일 끝).
보조: 주석 제거본 `scan/Spt1.code.lean` grep(탈출구·옵션), `decls_cls.json`(file=='Spt1') 통계, git log/show(`e52217bf`), Mathlib 트리 grep(이름 존재 확인), Python 점 개수 계산(y²=x³+3 over F₇ → 13점). 기계적 반복 블록을 훑어보기(skim)로 처리한 범위 없음(모든 범위를 읽음; 단 `Spt1ModularCRT` 6377–6653과 PART E 재수출 6174–6370은 내용이 단순 래퍼임을 확인하는 수준으로 읽음).
