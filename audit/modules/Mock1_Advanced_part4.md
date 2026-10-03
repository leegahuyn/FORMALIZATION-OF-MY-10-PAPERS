# Mock1_Advanced — Part 4 (L49201–70000) 범위 감사 [완료]

범위 통계 (decls_cls.json): 선언 1781개 = theorem 1484 (접근자 598 + 비접근자 886, 비접근자 중 597은 `:= X.y_at …` 전방적용), def 229, structure 68.
구간 구조: **49201–64159 (≈14,960행) = 재진술/전방 스캐폴딩**, **64160–70000 (≈5,840행) = 유한 구체 데이터 + 자기감사(self-audit) 층**.
49201–64159 구간에서 실제 전술(ring/linarith/norm_num/induction/omega…)은 단 2회(`decide`로 리스트 길이 확인). 새 수학 0.

## 2. 헤드라인 정리 (범위 내)
| 행 | 이름 | 내용(요약) | 상태 |
|---|---|---|---|
| 68301 | `advanced_claims_ii_ramanujan_f_prefix_table` | 3차 mock theta f(q)=Σq^{n²}/(-q;q)_n² 계수 16개 = [1,1,-2,3,-3,3,-5,7,-6,6,-10,12,-11,13,-17,20] (`decide`) | U (유한계산; OEIS A000025와 일치, python으로 20항 재확인) |
| 68622 | `advanced_claims_ii_ramanujan_finite_inside_outside_identity` | r<16: f(q⁻¹)계수 = 2ψ − S, S=Σ(-1)^n q^{n(n+1)/2}/(-q;q)²_∞ — 두 급수를 독립 정의 후 16계수 일치 | U (유한; python으로 60계수까지 성립 확인 → 참 항등식으로 보이나 전 차수 증명 없음) |
| 68499 | `advanced_claims_ii_ramanujan_denominator_stable_above_degree` | 분모 역수 계수의 안정성 (r<n+1) | U (작음) |
| 65741 | `advanced_claims_ii_signed_pair_list_norm_lower_bound` | Σ(a−b)²/2 ≤ Σ(a²+b²) (리스트 귀납+nlinarith) → `…pair_assignment_minimality` L65872: [I₁₁|−I₁₁]c=e₁ 의 최소노름 1/2 | U (쉬움) |
| 66084 | `advanced_claims_ii_appell_lerch_ridge_total_negative` | E(n,m)=n²/2+n(1+m)+m/2, ridge n=−1−m ⇒ 1/4+E = −(2m²+2m+1)/4 < 0 (∀m) | U (대수, 쉬움) |
| 66243–66317 | `advanced_claims_ii_unary_theta_partner_*`, `…coefficient_*_eighths` | 특성 (a,b)=(1/2,0) raw unary theta는 k↦−k−1 로 쌍상쇄 → 대칭 창 계수 0 | U (자명 대수; 논문 raw 식이 0으로 소멸함을 기록) |
| 64971–65008 | `advanced_claims_ii_paper_i2_forward_difference_table`, `…coefficient_is_forward_difference_residue` | 논문 Mahler 계수 [1,4,3,11,11,9] = 전진차분 [1,4,3,−14,36,−91] mod 25 | U (유한) |
| 64710 | `advanced_claims_ii_paper_i2_claimed_extrapolation_tube_false` | 외삽값 [9,1,7,14,24] ∉ 25ℤ ⇒ 논문의 tail 주장 반증 | U (단, MahlerEval이 이미 mod 25 환원값이라 사실상 자명) |
| 64952 | `advanced_claims_ii_paper_i2_mahler_matrix_not_upper_triangular` | B(n,j)=C(n,j)는 하삼각, 논문 "상삼각" 표기 오류 | U (자명) |
| 66797 / 67046 | `…item1_character_parity_mismatch`, `…item1_near_zero_criterion_fails` | χ₋₄(−1)=−1 vs ν=0 패리티 +1 불일치; 피적분 지수 −3/2<−1, 논문 조건 α<−1/2 는 수렴조건 α>−1/2와 정반대 | U (산술; "수렴 기준"은 유리수 부등식 정의일 뿐 Mathlib 적분가능성과 연결 없음) |
| 69699 / 69714 | `advanced_claims_ii_entropy_cardy_conventions_factor_four`, `…i6_counting_majorant_unbounded` | 파일 내 두 Cardy 상수 규약이 4배 차이; Thm I.6 증명의 계수 majorant = N (유계 아님) | U (자명; 논문 증명 결함 기록) |
| 68879 | `advanced_claims_ii_rlf_synthetic_object_not_ramanujan_f` | 헤드라인 번들이 쓰는 RLF 객체(kind=jacobi)는 Ramanujan f 가 아님 | U/T — 코드 스스로 "본체 인증서는 placeholder" 임을 증명 |
| 64774, 67537, 68943, 69876 | `…_input_manifest_incomplete` 4종 | Bool manifest(실제 q-급수/shadow/level/Kuznetsov/Weil/완비화/Rademacher tail/엔트로피 점근 = false) 미완 | T (정직한 gap 표기, 수학 아님) |
| 54439–59700 | `reference_advanced_claims_ii_*` (~540개) | 퇴화 reference 인증서 필드 전방 | A |
| 49252–54431 | `promptBulletStatement`, `finalTheoremAggregation` 등 | Closure/Spine/FinalAudit 재조립 | A/T |

## 4. 조건부 인증 감사 (범위 내 가설/인증서)
- **재진술 Prop-structure ~45개** (AdvancedClaimsIIRlfEndToEndClosureCertificate L49649 … FinalTheoremAggregationCertificate L54022, ReferenceAtomicChecklist L56498, FormulaLevelPromptLedger L58381, Rlf{FormulaProjection, RademacherKernelMath L60854, RademacherCoefficientMath, EnrichedMathematicalContent, FullMathematicalRow, PointwiseMathematicalPayload, MicrolocalMath L62125, ExplicitMathematicalSpine}, Front/Explicit MathStatement L63154–64074): 필드가 이미 증명된 앞층 필드의 사본 → **CIRCULAR(동어반복)/DISCHARGED-by-projection**. 가정으로서 정보량 0. 대상은 퇴화 reference (`referencePaperInstancesHRflConcrete` = part3의 `exactEntropyCoeff 1 0` 기반 jacobi 객체, `referenceAdvancedClaimsIICompletionCertificate` L39902).
- `AdvancedClaimsIIExactAnalyticBoundaryFormula` L68048: kuznetsov/weil/lvalue 필드 = reference에서 `True` (L67574–67584에서 코드가 `= True` 를 rfl로 자인) → **SUSPECT-VACUOUS (공허한 명명 경계)**.
- `referenceRademacherAlphaExtraction.cEqualsOne := True` (L25584; L69741에서 자인) → 공허.
- `AdvancedClaimsIIRamanujanFAbstractProofInput` L69130 / `ConcreteProofInput` L69218: 실제 f(q) 객체를 고정하고 나머지를 입력으로 받는 생성자. `entropyProof : EntropyGrowth f.coeff α β` 는 **SUBSTANTIVE** (Andrews–Dragonette/Bringmann–Ono 점근으로 참이나 미증명); 그러나 함께 요구되는 AppellLerch/Xi/Slash/RademacherExpansion 인증서는 part1에서 본 대로 임의 함수 필드라 **사소하게 충족 가능**(Rademacher 확장은 n마다 expansion 선택 가능). 인스턴스는 범위 내 미구성(manifest가 막음) — 정직.
- 범위 내 DISCHARGED: 64160–70000의 모든 유한 인증서 (PaperI2PAdicFinite L64435, RlfPaperI2ConcreteFinite L65056, PaperI2SPTArithmetic L65405, T1T2Reduced/FullSignedIdentity L65526/65900, AppellLerchFiniteLattice L66117, UnaryThetaRawFinite L66319, T3BlockPortfolio L66629, Item1KernelCuspAudit L67059, PaperKExactInputAudit L67611, Table6EntropyFinite L67778, RamanujanF{ConcreteFinite, InsideOutsideFinite, ConcreteFiniteBridge, PAdicFinite}, EntropyPaperInputAudit L69883) — 각각 `reference_…` 정리로 실제 증명됨. 내용은 유한 산술.

### reference 인스턴스: 퇴화 vs 실물
- **실물**: `referenceAdvancedClaimsIIRamanujanFPaperObject` L68326 (kind mockTheta, 계수 = 정확한 f(q) 계수 함수) — **Mock1_Advanced 전체에서 처음으로 진짜 mock theta 객체**(계수 수준; Mathlib PowerSeries와의 연결은 없음). f(q⁻¹), ψ(Kronecker형 문자), S 보정급수도 실물. χ₋₄ 표, p=5,k=2,M=50 SPT/Tor 두께 min(v_p,k), [I₁₁|−I₁₁] 행렬도 실물(사소).
- **논문 수치 하드코딩**: Paper I.2 표 [1,5,12,8,15,0] (q-급수 미유도, `actualQSeriesSpecified := false`; L69539에서 f(q) mod 25 = [1,1,23,3,22,3] 과 불일치 증명), Table 6 소수값(유리수 변환, diagnosticOnly), cusp 잔차 3e-13 등.
- **퇴화**: `referenceAdvancedClaimsIIPaperI2Overlap/Chart` left=right 동일함수 (합동 자명, L64726 자인); `referenceAdvancedClaimsIIPaperI2Normalization` raw=normalized; `referenceAdvancedClaimsIIPaperItem1KernelRecord.slashAction := fun _ _ => 1` L66880; TS phase rows `tableValue=computedValue=1` by rfl; `FinitePhaseMatch.phaseCompatible := True` L66941; exact 계수/L값/국소인자/전역상수 = 1 (L67544–67572, 코드가 "unit model"로 자인).
- **결정적 사실**: Ramanujan f 실물은 헤드라인 `AdvancedClaimsIICompletionCertificate`/`Unconditional…` 번들에 **연결되지 않음** — 번들은 계속 합성 객체를 사용하며 L68879가 두 객체가 다름을 증명.

## 5. 정의 충실도
- Ramanujan f: `AdvancedClaimsIIRamanujanDenominatorInvCoeff` L68251 = [q^r]∏_{j≤n}(1+q^j)^{−2} 재귀 ((1+X)^{−2}=Σ(−1)^t(t+1)X^t) — 정확. 단 `QSeries = Nat → R` 함수일 뿐 Mathlib `PowerSeries`와의 동치 정리 없음.
- f(q⁻¹) = Σ q^n/(−q;q)_n²: q-역전 지수 −n²+n(n+1)=n (L68495)로 정당화 — 형식적 계산으로 올바름.
- Tor: 여전히 Nat surrogate (`TorSkeleton.order`, gcd); Mathlib Tor 아님.
- "수렴 기준" `AdvancedClaimsIIPaperItem1NearZeroPowerCriterion` = (−1 < p) 유리수 부등식 정의; Mathlib `integrableOn_Ioo_rpow_iff` 류와 연결 없음.
- Kloosterman/Bessel/Rademacher (60854–62980): part1의 임의-multiplier `KloostermanSum`, `BesselIHalfModel` 정의 펼침만.

## 6. 실질 수학 vs 스캐폴딩 (행 기준, 20,800행)
- 49201–64159 (71.9%): 재진술 구조체·`_at` 접근자·`reference_*` 전방·`def … where f := C.x` → 스캐폴딩 ~100%.
- 64160–70000 (28.1%): 구조체 정의 1,429행 + reference 조립/접근자 ~1,556행 = 스캐폴딩; 계산 정의·계산 정리 ~2,200행이 실제 내용.
- **추정: 실질(유한 계산 + 자명~쉬운 대수 증명 + 정직한 반증 lemma) ≈ 9–11%, 깊은 수학 0%, 스캐폴딩 ≈ 89–91%.**

## 7. 수학적 정확성 / 과대표기
- 과대표기 이름: `…MathematicalContentCertificate`, `…MicrolocalMathCertificate`(미시국소해석 없음), `…ExplicitMathematicalSpine`, `…FrontMathStatement`, `advancedClaimsII_*ActualStatement`, `…FinalTheoremAggregation` — 전부 퇴화 reference 필드의 등식/문자열 비공백/List.Mem 재진술.
- `AdvancedClaimsIIRlfEntropyRegressionMathStatement` L60062: "log|c_n|−α√n+½log n → β" 는 reference 객체가 정의상 exp(√n−½log n) 이라 동어반복.
- 반대로 64160 이후는 논문 오류를 정확히 기록(외삽 tube 주장 거짓, Mahler 행렬 방향, χ 패리티 불일치, 근영점 적분 발산·α 조건 역전, Cardy 4배, Thm I.6 majorant 비유계, raw unary theta 소멸, I.2 표 ≠ f mod 25, level 1 vs 4 / conductor 1 vs 4 불일치 L67594–67609). 각 반증은 산술적으로 옳음(논문 원문 대조는 미실시).
- 범위 내 잘못된(거짓) 정리 없음 (컴파일 확인됨).

## 8. 코드 품질
- 15k행의 기계적 중복(같은 필드 등식이 Closure/Spine/Ledger/Front/Explicit 층마다 최대 5–8회 반복). `List.Mem.tail _ (List.Mem.tail _ …)` 수동 체인(L66470, 66509), 문자열 `sourceName` 필드. 범위 내 heartbeat 상향·Classical/Inhabited 트릭·custom syntax 없음. `decide` 는 ≤22원소 리스트/16계수 수준이라 안전.
- Mathlib PR 후보: 없음(Ramanujan f 계수를 `PowerSeries ℤ` 로 정식화하면 가치 있으나 현재 형태는 부적합).

## 10. 범위 잠정 점수
- 형식적 건전성 9 — sorry/axiom/트릭 없음, 컴파일 확인.
- 조건부 인증 정직성 5 — 72%는 퇴화 데이터를 "Mathematical/Final"로 포장(CIRCULAR 재진술), 28%는 Bool manifest·반증 lemma로 gap을 이례적으로 정직하게 공개.
- 수학적 실질성 2 — 실물 Ramanujan f 계수·16항 항등식 외엔 자명 산술.
- 정의 충실도 4 — f(q)·χ₋₄는 충실, 나머지(Tor, slash, Kloosterman, 수렴기준)는 proxy이고 bridge 없음.
- 코드 품질 2 — 극심한 중복, 재진술 층 남발.
- 종합 3.

## Coverage log
- 49201–49650 정독 (closure defs, promptBulletStatement). 49649–49700, 50380–50500 정독 (RlfEndToEndClosure, ActualStatement defs).
- 49700–54400: 구조체·def 목록 python 매핑 + 표본 정독(54400–54470); `_at` 접근자 런(49805–54369) skim.
- 54439–59700: `reference_*` 전방 정리 런 python 매핑 + 표본(55540–55600, 57640–57680) — skim.
- 59580–63153: 60018–60100, 60854–60935, 62125–62180, 62895–62990 정독, 나머지 python/본문 패턴 skim (by calc 1건 확인: 등식 전이).
- 63154–64159: 63224–63310, 63423–63470, 63530–63600 정독, 나머지 skim.
- 64160–70000: **전부 정독** (Read 64160–70006).
- 보조: Ramanujan f / inside–outside 항등식 python 수치 검증 (scratchpad/ramf.py).
