import Proofs.Defs

set_option maxHeartbeats 400000

open Classical in
noncomputable def ctDelta {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Finset X :=
  Finset.univ.filter (fun e => ∃ a ∈ A, ∃ b ∈ A, a e ≠ b e ∧ ∀ x, e < x → a x = b x)

def ctPeak {X : Type*} [LinearOrder X] (A : Finset (X → Bool)) : Prop :=
  ∃ d : X, (∀ x, d < x → ∀ a ∈ A, ∀ b ∈ A, a x = b x) ∧
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ e ∈ A, a ≠ b ∧ c ≠ e ∧
      a d = false ∧ b d = false ∧ c d = true ∧ e d = true

open Classical in
noncomputable def ctColor {X : Type*} [LinearOrder X] [Fintype X]
    (χ : Finset X → Fin 2) (A : Finset (X → Bool)) : Fin 2 :=
  if ctPeak A then 1 else χ (ctDelta A)

def ctReal {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (E : Finset X) : Prop :=
  ∀ T : Finset X, T ⊆ E → ∃ A : Finset (X → Bool),
    A ⊆ K ∧ A.card = T.card + 1 ∧ ctDelta A = T ∧ ¬ ctPeak A

lemma ct_mem_delta {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (e : X) :
    e ∈ ctDelta A ↔ ∃ a ∈ A, ∃ b ∈ A, a e ≠ b e ∧ ∀ x, e < x → a x = b x := by
  unfold ctDelta
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩

lemma ct_peak_iff {X : Type*} [LinearOrder X] (A : Finset (X → Bool)) :
    ctPeak A ↔ ∃ d : X, (∀ x, d < x → ∀ a ∈ A, ∀ b ∈ A, a x = b x) ∧
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ e ∈ A, a ≠ b ∧ c ≠ e ∧
        a d = false ∧ b d = false ∧ c d = true ∧ e d = true := Iff.rfl

lemma ct_color_peak {X : Type*} [LinearOrder X] [Fintype X]
    (χ : Finset X → Fin 2) (A : Finset (X → Bool)) (h : ctPeak A) :
    ctColor χ A = 1 := by
  unfold ctColor
  simp only [if_pos h]

lemma ct_color_np {X : Type*} [LinearOrder X] [Fintype X]
    (χ : Finset X → Fin 2) (A : Finset (X → Bool)) (h : ¬ ctPeak A) :
    ctColor χ A = χ (ctDelta A) := by
  unfold ctColor
  simp only [if_neg h]

lemma ct_bool3 : ∀ x y z : Bool, x ≠ z → y ≠ z → x = y := by decide

lemma ct_two (q c : ℕ) (hq : 0 < q) (h : q * 2 < 2 * c) : 1 < c := by omega

lemma ct_half (q a b c : ℕ) (h : q * 2 < 2 * c) (hc : c ≤ a + b) :
    q < 2 * a ∨ q < 2 * b := by omega

lemma ct_arith (a b c n : ℕ) (h1 : a ≤ 2 * b) (h2 : b + 1 ≤ n) (h3 : c = n) :
    a < 2 * c := by omega

lemma ct_pow (t : ℕ) : 2 ^ t ≤ 2 * 2 ^ (t - 1) := by
  cases t with
  | zero => norm_num
  | succ k =>
    rw [Nat.add_sub_cancel, pow_succ]
    exact le_of_eq (Nat.mul_comm _ _)

lemma ct_ne {X : Type*} (u v : X → Bool) (d : X) (hu : u d = false) (hv : v d = true) :
    u ≠ v := by
  intro h
  rw [h] at hu
  exact Bool.false_ne_true (hu.symm.trans hv)

lemma ct_real_base {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (a : X → Bool) (ha : a ∈ K) : ctReal K ∅ := by
  intro T hT
  have hT0 : T = ∅ := Finset.subset_empty.mp hT
  subst hT0
  refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, by simp, ?_, ?_⟩
  · ext e
    constructor
    · intro he
      obtain ⟨u, hu, v, hv, hne, _⟩ := (ct_mem_delta _ e).mp he
      rw [Finset.mem_singleton] at hu hv
      exact absurd (by rw [hu, hv]) hne
    · intro h
      exact absurd h (by simp)
  · intro hP
    obtain ⟨d, _, u, hu, v, hv, _, _, _, _, huv, _⟩ := (ct_peak_iff _).mp hP
    rw [Finset.mem_singleton] at hu hv
    exact huv (hu.trans hv.symm)

lemma ct_delta_insert {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (p : X → Bool) (d : X)
    (hne : A.Nonempty) (h1 : ∀ a ∈ A, a d ≠ p d)
    (h2 : ∀ a ∈ A, ∀ x, d < x → a x = p x) :
    ctDelta (insert p A) = insert d (ctDelta A) := by
  have key : ∀ a ∈ A, ∀ e : X, a e ≠ p e → (∀ x, e < x → a x = p x) → e = d := by
    intro a ha e hne' hag
    rcases lt_trichotomy e d with h | h | h
    · exact absurd (hag d h) (h1 a ha)
    · exact h
    · exact absurd (h2 a ha e h) hne'
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, b, hb, hab, hag⟩ := (ct_mem_delta _ e).mp he
    rcases Finset.mem_insert.mp ha with hap | haA
    · rcases Finset.mem_insert.mp hb with hbp | hbA
      · exact absurd (by rw [hap, hbp]) hab
      · refine Finset.mem_insert.mpr
          (Or.inl (key b hbA e (fun h => hab ?_) (fun x hx => ?_)))
        · rw [hap]
          exact h.symm
        · have h3 := hag x hx
          rw [hap] at h3
          exact h3.symm
    · rcases Finset.mem_insert.mp hb with hbp | hbA
      · refine Finset.mem_insert.mpr
          (Or.inl (key a haA e (fun h => hab ?_) (fun x hx => ?_)))
        · rw [hbp]
          exact h
        · have h3 := hag x hx
          rw [hbp] at h3
          exact h3
      · exact Finset.mem_insert.mpr
          (Or.inr ((ct_mem_delta A e).mpr ⟨a, haA, b, hbA, hab, hag⟩))
  · intro he
    rcases Finset.mem_insert.mp he with hed | he'
    · obtain ⟨a, ha⟩ := hne
      exact (ct_mem_delta _ e).mpr
        ⟨a, Finset.mem_insert_of_mem ha, p, Finset.mem_insert_self p A,
          by rw [hed]; exact h1 a ha, by rw [hed]; exact h2 a ha⟩
    · obtain ⟨a, ha, b, hb, hab, hag⟩ := (ct_mem_delta A e).mp he'
      exact (ct_mem_delta _ e).mpr
        ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb, hab, hag⟩

lemma ct_np_insert {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (p : X → Bool) (d : X)
    (h1 : ∀ a ∈ A, a d ≠ p d)
    (h2 : ∀ a ∈ A, ∀ x, d < x → a x = p x) :
    ¬ ctPeak (insert p A) := by
  intro hP
  obtain ⟨d', hag, a, ha, b, hb, c, hc, e, he, hab, hce, had, hbd, hcd, hed⟩ :=
    (ct_peak_iff _).mp hP
  have hall : ∀ u ∈ insert p A, ∀ x, d < x → u x = p x := by
    intro u hu x hx
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h]
    · exact h2 u h x hx
  have honly : ∀ u ∈ insert p A, u d = p d → u = p := by
    intro u hu hud
    rcases Finset.mem_insert.mp hu with h | h
    · exact h
    · exact absurd hud (h1 u h)
  rcases lt_trichotomy d' d with h | h | h
  · have hu : ∃ u ∈ A, u ∈ insert p A := by
      rcases Finset.mem_insert.mp ha with h' | h'
      · rcases Finset.mem_insert.mp hb with h'' | h''
        · exact absurd (h'.trans h''.symm) hab
        · exact ⟨b, h'', hb⟩
      · exact ⟨a, h', ha⟩
    obtain ⟨u, huA, hu'⟩ := hu
    exact h1 u huA (hag d h u hu' p (Finset.mem_insert_self p A))
  · rw [h] at had hbd hcd hed
    cases hp : p d with
    | false =>
      have e1 := honly a ha (had.trans hp.symm)
      have e2 := honly b hb (hbd.trans hp.symm)
      exact hab (e1.trans e2.symm)
    | true =>
      have e1 := honly c hc (hcd.trans hp.symm)
      have e2 := honly e he (hed.trans hp.symm)
      exact hce (e1.trans e2.symm)
  · have e1 := hall a ha d' h
    have e2 := hall c hc d' h
    exact Bool.false_ne_true (had.symm.trans (e1.trans (e2.symm.trans hcd)))

lemma ct_top {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (a b : X → Bool) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b) :
    ∃ d : X, (∃ u ∈ K, ∃ v ∈ K, u d ≠ v d) ∧
      ∀ x, d < x → ∀ u ∈ K, ∀ v ∈ K, u x = v x := by
  classical
  have hne : ((Finset.univ : Finset X).filter
      (fun x => ∃ u ∈ K, ∃ v ∈ K, u x ≠ v x)).Nonempty := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hab
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, a, ha, b, hb, hx⟩⟩
  refine ⟨Finset.max' _ hne, (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2, ?_⟩
  intro x hx u hu v hv
  by_contra hne'
  have hxm : x ∈ (Finset.univ : Finset X).filter
      (fun x => ∃ u ∈ K, ∃ v ∈ K, u x ≠ v x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ x, u, hu, v, hv, hne'⟩
  exact absurd (Finset.le_max' _ x hxm) (not_le.mpr hx)

lemma ct_step {X : Type*} [LinearOrder X] [Fintype X]
    (K K' : Finset (X → Bool)) (E : Finset X) (p : X → Bool) (d : X)
    (hK' : K' ⊆ K) (hp : p ∈ K)
    (h1 : ∀ a ∈ K', a d ≠ p d)
    (h2 : ∀ x, d < x → ∀ u ∈ K, ∀ v ∈ K, u x = v x)
    (hR : ctReal K' E) : d ∉ E ∧ ctReal K (insert d E) := by
  constructor
  · intro hdE
    obtain ⟨A, hA, _, hAd, _⟩ := hR {d} (Finset.singleton_subset_iff.mpr hdE)
    have hd : d ∈ ctDelta A := by
      rw [hAd]
      exact Finset.mem_singleton_self d
    obtain ⟨a, ha, b, hb, hab, _⟩ := (ct_mem_delta A d).mp hd
    have e1 := h1 a (hA ha)
    have e2 := h1 b (hA hb)
    exact hab (ct_bool3 (a d) (b d) (p d) e1 e2)
  · intro T hT
    by_cases hdT : d ∈ T
    · have hsubE : T.erase d ⊆ E := by
        intro x hx
        obtain ⟨hxd, hxT⟩ := Finset.mem_erase.mp hx
        rcases Finset.mem_insert.mp (hT hxT) with h | h
        · exact absurd h hxd
        · exact h
      obtain ⟨A, hA, hAc, hAd, _⟩ := hR (T.erase d) hsubE
      have h1' : ∀ a ∈ A, a d ≠ p d := fun a ha => h1 a (hA ha)
      have h2' : ∀ a ∈ A, ∀ x, d < x → a x = p x :=
        fun a ha x hx => h2 x hx a (hK' (hA ha)) p hp
      have hpA : p ∉ A := fun h => h1' p h rfl
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      refine ⟨insert p A, ?_, ?_, ?_, ct_np_insert A p d h1' h2'⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]
          exact hp
        · exact hK' (hA h)
      · have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨d, hdT⟩
        have hTe := Finset.card_erase_of_mem hdT
        have hins := Finset.card_insert_of_notMem hpA
        omega
      · rw [ct_delta_insert A p d hAne h1' h2', hAd]
        exact Finset.insert_erase hdT
    · have hsubE : T ⊆ E := by
        intro x hx
        rcases Finset.mem_insert.mp (hT hx) with h | h
        · exact absurd (by rw [← h]; exact hx) hdT
        · exact h
      obtain ⟨A, hA, hAc, hAd, hAp⟩ := hR T hsubE
      exact ⟨A, hA.trans hK', hAc, hAd, hAp⟩

lemma ct_cat {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool), K.card = n + 1 →
      (∀ A : Finset (X → Bool), A ⊆ K → ¬ ctPeak A) →
      ∃ E : Finset X, E.card = n ∧ ctReal K E := by
  intro n
  induction n with
  | zero =>
    intro K hK _
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
    exact ⟨∅, Finset.card_empty, ct_real_base K a ha⟩
  | succ n ih =>
    intro K hK hH
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < K.card)
    obtain ⟨d, ⟨u, hu, v, hv, huv⟩, hag⟩ := ct_top K a b ha hb hab
    have hex : ∃ p ∈ K, ∀ w ∈ K.erase p, w d ≠ p d := by
      by_contra hno
      push_neg at hno
      obtain ⟨u', hu', hud⟩ := hno u hu
      obtain ⟨v', hv', hvd⟩ := hno v hv
      obtain ⟨hu'n, hu'K⟩ := Finset.mem_erase.mp hu'
      obtain ⟨hv'n, hv'K⟩ := Finset.mem_erase.mp hv'
      apply hH K (Finset.Subset.refl K)
      cases hu0 : u d with
      | false =>
        cases hv0 : v d with
        | false => exact absurd (hu0.trans hv0.symm) huv
        | true =>
          exact (ct_peak_iff K).mpr ⟨d, hag, u, hu, u', hu'K, v, hv, v', hv'K,
            fun h => hu'n h.symm, fun h => hv'n h.symm,
            hu0, hud.trans hu0, hv0, hvd.trans hv0⟩
      | true =>
        cases hv0 : v d with
        | false =>
          exact (ct_peak_iff K).mpr ⟨d, hag, v, hv, v', hv'K, u, hu, u', hu'K,
            fun h => hv'n h.symm, fun h => hu'n h.symm,
            hv0, hvd.trans hv0, hu0, hud.trans hu0⟩
        | true => exact absurd (hu0.trans hv0.symm) huv
    obtain ⟨p, hp, hpd⟩ := hex
    have hcard : (K.erase p).card = n + 1 := by
      rw [Finset.card_erase_of_mem hp]
      omega
    obtain ⟨E, hE, hR⟩ := ih (K.erase p) hcard
      (fun A hA => hH A (hA.trans (Finset.erase_subset p K)))
    obtain ⟨hdE, hR'⟩ :=
      ct_step K (K.erase p) E p d (Finset.erase_subset p K) hp hpd hag hR
    refine ⟨insert d E, ?_, hR'⟩
    have hins := Finset.card_insert_of_notMem hdE
    omega

lemma ct_deep {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool), 2 ^ n < 2 * K.card →
      ∃ E : Finset X, E.card = n ∧ ctReal K E := by
  intro n
  induction n with
  | zero =>
    intro K hK
    rw [pow_zero] at hK
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
    exact ⟨∅, Finset.card_empty, ct_real_base K a ha⟩
  | succ n ih =>
    intro K hK
    rw [pow_succ] at hK
    have hq : 0 < 2 ^ n := pow_pos (by norm_num) n
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (ct_two (2 ^ n) K.card hq hK)
    obtain ⟨d, ⟨u, hu, v, hv, huv⟩, hag⟩ := ct_top K a b ha hb hab
    obtain ⟨pf, hpf, hpfd, pt, hpt, hptd⟩ :
        ∃ pf ∈ K, pf d = false ∧ ∃ pt ∈ K, pt d = true := by
      cases hu0 : u d with
      | false =>
        cases hv0 : v d with
        | false => exact absurd (hu0.trans hv0.symm) huv
        | true => exact ⟨u, hu, hu0, v, hv, hv0⟩
      | true =>
        cases hv0 : v d with
        | false => exact ⟨v, hv, hv0, u, hu, hu0⟩
        | true => exact absurd (hu0.trans hv0.symm) huv
    have hsplit : K.card ≤ (K.filter (fun w => w d = true)).card +
        (K.filter (fun w => w d = false)).card := by
      have hsub : K ⊆ K.filter (fun w => w d = true) ∪
          K.filter (fun w => w d = false) := by
        intro w hw
        cases hwd : w d with
        | false =>
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, hwd⟩)
        | true =>
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hwd⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rcases ct_half (2 ^ n) _ _ K.card hK hsplit with h | h
    · obtain ⟨E, hE, hR⟩ := ih (K.filter (fun w => w d = true)) h
      have h1 : ∀ w ∈ K.filter (fun w => w d = true), w d ≠ pf d := by
        intro w hw
        rw [(Finset.mem_filter.mp hw).2, hpfd]
        decide
      obtain ⟨hdE, hR'⟩ :=
        ct_step K (K.filter (fun w => w d = true)) E pf d
          (Finset.filter_subset _ K) hpf h1 hag hR
      refine ⟨insert d E, ?_, hR'⟩
      have hins := Finset.card_insert_of_notMem hdE
      omega
    · obtain ⟨E, hE, hR⟩ := ih (K.filter (fun w => w d = false)) h
      have h1 : ∀ w ∈ K.filter (fun w => w d = false), w d ≠ pt d := by
        intro w hw
        rw [(Finset.mem_filter.mp hw).2, hptd]
        decide
      obtain ⟨hdE, hR'⟩ :=
        ct_step K (K.filter (fun w => w d = false)) E pt d
          (Finset.filter_subset _ K) hpt h1 hag hR
      refine ⟨insert d E, ?_, hR'⟩
      have hins := Finset.card_insert_of_notMem hdE
      omega

lemma ct_peak_four {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (hP : ctPeak A) :
    ∃ B : Finset (X → Bool), B ⊆ A ∧ B.card = 4 ∧ ctPeak B := by
  obtain ⟨d, hag, a, ha, b, hb, c, hc, e, he, hab, hce, had, hbd, hcd, hed⟩ :=
    (ct_peak_iff A).mp hP
  have hac : a ≠ c := ct_ne a c d had hcd
  have hae : a ≠ e := ct_ne a e d had hed
  have hbc : b ≠ c := ct_ne b c d hbd hcd
  have hbe : b ≠ e := ct_ne b e d hbd hed
  have hsub : insert a (insert b (insert c ({e} : Finset (X → Bool)))) ⊆ A := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | hx
    · rw [h]
      exact ha
    · rcases Finset.mem_insert.mp hx with h | hx
      · rw [h]
        exact hb
      · rcases Finset.mem_insert.mp hx with h | hx
        · rw [h]
          exact hc
        · rw [Finset.mem_singleton.mp hx]
          exact he
  have h3 : c ∉ ({e} : Finset (X → Bool)) :=
    fun h => hce (Finset.mem_singleton.mp h)
  have h2 : b ∉ insert c ({e} : Finset (X → Bool)) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hbc h
    · exact hbe (Finset.mem_singleton.mp h)
  have h1 : a ∉ insert b (insert c ({e} : Finset (X → Bool))) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hab h
    · rcases Finset.mem_insert.mp h with h | h
      · exact hac h
      · exact hae (Finset.mem_singleton.mp h)
  refine ⟨insert a (insert b (insert c ({e} : Finset (X → Bool)))), hsub, ?_, ?_⟩
  · have e1 := Finset.card_insert_of_notMem h1
    have e2 := Finset.card_insert_of_notMem h2
    have e3 := Finset.card_insert_of_notMem h3
    have e4 : ({e} : Finset (X → Bool)).card = 1 := Finset.card_singleton e
    omega
  · exact (ct_peak_iff _).mpr ⟨d,
      fun x hx u hu v hv => hag x hx u (hsub hu) v (hsub hv),
      a, Finset.mem_insert_self _ _,
      b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      c, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
      e, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self e))),
      hab, hce, had, hbd, hcd, hed⟩

theorem stepping_up_caterpillar : ∀ {X : Type*} [LinearOrder X] [Fintype X] (s t : ℕ) (χ : Finset X → Fin 2), Solon.NoMono χ 3 s 0 → Solon.NoMono χ 3 t 1 → ∃ ψ : Finset (X → Bool) → Fin 2, ∀ m n : ℕ, s + 1 ≤ m → 2 ^ (t - 1) + 1 ≤ n → Solon.NoMono ψ 4 m 0 ∧ Solon.NoMono ψ 4 n 1 := by
  intro X _ _ s t χ hχ0 hχ1
  refine ⟨ctColor χ, ?_⟩
  intro m n hm hn
  constructor
  · intro K hK
    obtain ⟨K', hK'K, hK'c⟩ :=
      Finset.exists_subset_card_eq (show s + 1 ≤ K.card by omega)
    by_contra hno
    have hmono : ∀ A : Finset (X → Bool), A ⊆ K' → A.card = 4 →
        ctColor χ A = 0 := by
      intro A hA hAc
      by_contra hne
      exact hno ⟨A, Finset.mem_powersetCard.mpr ⟨hA.trans hK'K, hAc⟩, hne⟩
    have hH : ∀ A : Finset (X → Bool), A ⊆ K' → ¬ ctPeak A := by
      intro A hA hP
      obtain ⟨B, hBA, hBc, hBP⟩ := ct_peak_four A hP
      have h0 := hmono B (hBA.trans hA) hBc
      rw [ct_color_peak χ B hBP] at h0
      exact absurd h0 (by decide)
    obtain ⟨E, hE, hR⟩ := ct_cat s K' hK'c hH
    obtain ⟨T, hT, hTne⟩ := hχ0 E hE
    obtain ⟨hTE, hTc⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨A, hA, hAc, hAd, hAp⟩ := hR T hTE
    have h0 := hmono A hA (by omega)
    rw [ct_color_np χ A hAp, hAd] at h0
    exact hTne h0
  · intro K hK
    by_contra hno
    have hmono : ∀ A : Finset (X → Bool), A ⊆ K → A.card = 4 →
        ctColor χ A = 1 := by
      intro A hA hAc
      by_contra hne
      exact hno ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hAc⟩, hne⟩
    obtain ⟨E, hE, hR⟩ := ct_deep t K
      (ct_arith (2 ^ t) (2 ^ (t - 1)) K.card n (ct_pow t) hn hK)
    obtain ⟨T, hT, hTne⟩ := hχ1 E hE
    obtain ⟨hTE, hTc⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨A, hA, hAc, hAd, hAp⟩ := hR T hTE
    have h0 := hmono A hA (by omega)
    rw [ct_color_np χ A hAp, hAd] at h0
    exact hTne h0

