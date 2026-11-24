import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1635

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val (gs : List Gate) (x : List Bool) (Y : ℕ) : Bool :=
  (gs.foldl step x).getD Y false

lemma eval_eq (gs : List Gate) (Y : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, Y⟩ x = val gs x Y := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    · simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

lemma val_input (gs : List Gate) (x : List Bool) (Y : ℕ) (hY : Y < x.length) :
    val gs x Y = x.getD Y false :=
  foldl_getD_lt gs x Y hY

lemma val_big (gs : List Gate) (x : List Bool) (Y : ℕ) (hY : x.length + gs.length ≤ Y) :
    val gs x Y = false := by
  unfold val
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [foldl_length]
    exact hY

lemma val_gate (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < gs.length)
    (hwf : ∀ a ∈ (gs[i]).inputs, a < x.length + i) :
    val gs x (x.length + i) = (gs[i]).op.eval ((gs[i]).inputs.map (val gs x)) := by
  have hsplit : gs = gs.take i ++ gs[i] :: gs.drop (i + 1) := by simp
  have hlen : ((gs.take i).foldl step x).length = x.length + i := by
    rw [foldl_length, List.length_take]
    omega
  have hpre : ∀ a, a < x.length + i →
      val gs x a = ((gs.take i).foldl step x).getD a false := by
    intro a ha
    unfold val
    conv_lhs => rw [← List.take_append_drop i gs, List.foldl_append]
    exact foldl_getD_lt _ _ _ (by omega)
  have hmap : (gs[i]).inputs.map (val gs x) =
      (gs[i]).inputs.map (fun a => ((gs.take i).foldl step x).getD a false) :=
    List.map_congr_left fun a ha => hpre a (hwf a ha)
  rw [hmap]
  unfold val
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_getD_lt]
  · rw [← hlen]
    simp [step, List.getD_eq_getElem?_getD]
  · simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_ofFn {N : ℕ} (f : Fin N → Bool) (j : ℕ) (hj : j < N) :
    (List.ofFn f).getD j false = f ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, hj]

def Cl {N len : ℕ} (ev : ℕ → (Fin N → Bool) → Bool) (z : Fin N → Bool)
    (Tt : Fin N → Fin N → Bool) (Lt : Finset (Fin N)) (isOr : Fin len → Prop)
    (inp : Fin len → List ℕ) (m : ℕ) (X : Finset (Fin N)) : Prop :=
  ∀ i : Fin len, (i : ℕ) < m → isOr i → ev (N + (i : ℕ)) z = false →
    ∀ c1 c2 : ℕ, inp i = [c1, c2] → ∀ s ∈ Lt, ∀ s' ∈ Lt,
    (ev c1 (Tt s) = true ∨ ev c2 (Tt s) = true) →
    (ev c1 (Tt s') = true ∨ ev c2 (Tt s') = true) → (s ∈ X ↔ s' ∈ X)

def Sem {N len : ℕ} (ev : ℕ → (Fin N → Bool) → Bool) (z : Fin N → Bool)
    (Tt : Fin N → Fin N → Bool) (Lt : Finset (Fin N)) (isOr : Fin len → Prop)
    (inp : Fin len → List ℕ) : Prop :=
  (∀ v : Fin N, ev (v : ℕ) z = false → ∀ a ∈ Lt, ev (v : ℕ) (Tt a) = true → a = v) ∧
  (∀ w : ℕ, N + len ≤ w → ∀ x, ev w x = false) ∧
  (∀ i : Fin len,
    (¬ isOr i ∧ (∀ x, ev (N + (i : ℕ)) x = true → ∀ c ∈ inp i, ev c x = true) ∧
      (∀ x, ev (N + (i : ℕ)) x = false → ∃ c ∈ inp i, ev c x = false)) ∨
    (isOr i ∧ ∀ x, (ev (N + (i : ℕ)) x = true ↔ ∃ c ∈ inp i, ev c x = true))) ∧
  (∀ i : Fin len, (∀ c ∈ inp i, c < N + (i : ℕ)) ∧
    ((∃ c, inp i = [c]) ∨ ∃ c1 c2, inp i = [c1, c2]))

def Mrg {N len : ℕ} (ev : ℕ → (Fin N → Bool) → Bool) (z : Fin N → Bool)
    (Tt : Fin N → Fin N → Bool) (Lt : Finset (Fin N)) (isOr : Fin len → Prop)
    (inp : Fin len → List ℕ) (i : Fin len) : Prop :=
  isOr i ∧ ev (N + (i : ℕ)) z = false ∧
    ∃ w1 w2 : ℕ, inp i = [w1, w2] ∧ ∃ r ∈ Lt, ∃ r' ∈ Lt, ev w1 (Tt r) = true ∧
      ev w2 (Tt r') = true ∧
      ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ Cl ev z Tt Lt isOr inp (i : ℕ) X

section abs

variable {N len : ℕ} {ev : ℕ → (Fin N → Bool) → Bool} {z : Fin N → Bool}
  {Tt : Fin N → Fin N → Bool} {Lt : Finset (Fin N)} {isOr : Fin len → Prop}
  {inp : Fin len → List ℕ}

lemma Cl_mono {m m' : ℕ} (h : m ≤ m') {X : Finset (Fin N)}
    (hc : Cl ev z Tt Lt isOr inp m' X) : Cl ev z Tt Lt isOr inp m X :=
  fun i hi => hc i (lt_of_lt_of_le hi h)

lemma Cl_of_len {m : ℕ} {X : Finset (Fin N)}
    (hc : Cl ev z Tt Lt isOr inp len X) : Cl ev z Tt Lt isOr inp m X :=
  fun i _ => hc i i.2

lemma Cl_symmDiff {m : ℕ} {Y Z : Finset (Fin N)}
    (hY : Cl ev z Tt Lt isOr inp m Y) (hZ : Cl ev z Tt Lt isOr inp m Z) :
    Cl ev z Tt Lt isOr inp m (symmDiff Y Z) := by
  intro i hi hor hz c1 c2 hc s hs s' hs' h h'
  have e1 := hY i hi hor hz c1 c2 hc s hs s' hs' h h'
  have e2 := hZ i hi hor hz c1 c2 hc s hs s' hs' h h'
  simp only [Finset.mem_symmDiff]
  tauto

lemma Cl_inter {m : ℕ} {Y : Finset (Fin N)}
    (hY : Cl ev z Tt Lt isOr inp m Y) : Cl ev z Tt Lt isOr inp m (Y ∩ Lt) := by
  intro i hi hor hz c1 c2 hc s hs s' hs' h h'
  have e1 := hY i hi hor hz c1 c2 hc s hs s' hs' h h'
  simp only [Finset.mem_inter]
  tauto

lemma Cl_sdiff {m : ℕ} {Y : Finset (Fin N)}
    (hY : Cl ev z Tt Lt isOr inp m Y) : Cl ev z Tt Lt isOr inp m (Lt \ Y) := by
  intro i hi hor hz c1 c2 hc s hs s' hs' h h'
  have e1 := hY i hi hor hz c1 c2 hc s hs s' hs' h h'
  simp only [Finset.mem_sdiff]
  tauto

lemma S (hS : Sem ev z Tt Lt isOr inp) : ∀ w : ℕ, ev w z = false → ∀ a ∈ Lt, ∀ b ∈ Lt,
    ev w (Tt a) = true → ev w (Tt b) = true →
    ∀ X : Finset (Fin N), Cl ev z Tt Lt isOr inp (w + 1 - N) X → (a ∈ X ↔ b ∈ X) := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hz a ha b hb hTa hTb X hX
    by_cases hw : w < N
    · have e1 := h1 ⟨w, hw⟩ hz a ha hTa
      have e2 := h1 ⟨w, hw⟩ hz b hb hTb
      rw [e1, e2]
    · by_cases hw2 : w - N < len
      · obtain ⟨i, rfl⟩ : ∃ i : Fin len, w = N + (i : ℕ) :=
          ⟨⟨w - N, hw2⟩, by simp only; omega⟩
        obtain ⟨hlt, hshape⟩ := h4 i
        rcases h3 i with ⟨_, hand1, hand0⟩ | ⟨hor, horsem⟩
        · obtain ⟨c, hc, hcz⟩ := hand0 z hz
          have hcl := hlt c hc
          exact ih c hcl hcz a ha b hb (hand1 _ hTa c hc) (hand1 _ hTb c hc) X
            (Cl_mono (by omega) hX)
        · rcases hshape with ⟨c, hc⟩ | ⟨c1, c2, hc⟩
          · have hmem : c ∈ inp i := by rw [hc]; simp
            have hcz : ev c z = false := by
              by_contra hne
              have h := (horsem z).2 ⟨c, hmem, by simpa using hne⟩
              rw [hz] at h
              exact absurd h (by simp)
            have get : ∀ x, ev (N + (i : ℕ)) x = true → ev c x = true := by
              intro x hx
              obtain ⟨c', hc', h⟩ := (horsem x).1 hx
              rw [hc] at hc'
              have hcc : c' = c := by simpa using hc'
              rw [← hcc]
              exact h
            have hcl := hlt c hmem
            exact ih c hcl hcz a ha b hb (get _ hTa) (get _ hTb) X (Cl_mono (by omega) hX)
          · have get : ∀ x, ev (N + (i : ℕ)) x = true → ev c1 x = true ∨ ev c2 x = true := by
              intro x hx
              obtain ⟨c', hc', h⟩ := (horsem x).1 hx
              rw [hc] at hc'
              have hcc : c' = c1 ∨ c' = c2 := by simpa using hc'
              rcases hcc with rfl | rfl
              · exact Or.inl h
              · exact Or.inr h
            exact hX i (by omega) hor hz c1 c2 hc a ha b hb (get _ hTa) (get _ hTb)
      · rw [h2 w (by omega)] at hTa
        exact absurd hTa (by simp)

lemma or_inputs_false (hS : Sem ev z Tt Lt isOr inp) (i : Fin len) (hor : isOr i)
    (hz : ev (N + (i : ℕ)) z = false) (c : ℕ) (hc : c ∈ inp i) : ev c z = false := by
  obtain ⟨_, _, h3, _⟩ := hS
  rcases h3 i with ⟨hno, _⟩ | ⟨_, horsem⟩
  · exact absurd hor hno
  · by_contra hne
    have h := (horsem z).2 ⟨c, hc, by simpa using hne⟩
    rw [hz] at h
    exact absurd h (by simp)

lemma side (hS : Sem ev z Tt Lt isOr inp) (i : Fin len) (hor : isOr i)
    (hz : ev (N + (i : ℕ)) z = false) (c : ℕ) (hc : c ∈ inp i)
    (Y : Finset (Fin N)) (hY : Cl ev z Tt Lt isOr inp (i : ℕ) Y) :
    ∀ a ∈ Lt, ∀ b ∈ Lt, ev c (Tt a) = true → ev c (Tt b) = true → (a ∈ Y ↔ b ∈ Y) := by
  intro a ha b hb h h'
  have hcl := (hS.2.2.2 i).1 c hc
  exact S hS c (or_inputs_false hS i hor hz c hc) a ha b hb h h' Y (Cl_mono (by omega) hY)

lemma step_not (hS : Sem ev z Tt Lt isOr inp) (i : Fin len)
    (hn : ¬ Mrg ev z Tt Lt isOr inp i) (Y : Finset (Fin N))
    (hY : Cl ev z Tt Lt isOr inp (i : ℕ) Y) : Cl ev z Tt Lt isOr inp ((i : ℕ) + 1) Y := by
  intro j hj hor hz c1 c2 hc s hs s' hs' hhs hhs'
  by_cases hji : (j : ℕ) < (i : ℕ)
  · exact hY j hji hor hz c1 c2 hc s hs s' hs' hhs hhs'
  · have hjeq : j = i := Fin.ext (by omega)
    subst hjeq
    have m1 : c1 ∈ inp j := by rw [hc]; simp
    have m2 : c2 ∈ inp j := by rw [hc]; simp
    have S1 := side hS j hor hz c1 m1 Y hY
    have S2 := side hS j hor hz c2 m2 Y hY
    have cross : ∀ u ∈ Lt, ∀ u' ∈ Lt, ev c1 (Tt u) = true → ev c2 (Tt u') = true →
        (u ∈ Y ↔ u' ∈ Y) := by
      intro u hu u' hu' e1 e2
      by_contra hne
      apply hn
      by_cases huY : u ∈ Y
      · have hu'Y : u' ∉ Y := fun h => hne ⟨fun _ => h, fun _ => huY⟩
        exact ⟨hor, hz, c1, c2, hc, u, hu, u', hu', e1, e2, Y, huY, hu'Y, hY⟩
      · have hu'Y : u' ∈ Y := by
          by_contra h
          exact hne ⟨fun h' => absurd h' huY, fun h' => absurd h' h⟩
        exact ⟨hor, hz, c1, c2, hc, u, hu, u', hu', e1, e2, Lt \ Y,
          by simp [hu, huY], by simp [hu'Y], Cl_sdiff hY⟩
    rcases hhs with a1 | a2 <;> rcases hhs' with b1 | b2
    · exact S1 s hs s' hs' a1 b1
    · exact cross s hs s' hs' a1 b2
    · exact (cross s' hs' s hs b1 a2).symm
    · exact S2 s hs s' hs' a2 b2

open Classical in
noncomputable def C (ev : ℕ → (Fin N → Bool) → Bool) (z : Fin N → Bool)
    (Tt : Fin N → Fin N → Bool) (Lt : Finset (Fin N)) (isOr : Fin len → Prop)
    (inp : Fin len → List ℕ) (m : ℕ) : Finset (Finset (Fin N)) :=
  Lt.powerset.filter (fun Y => Cl ev z Tt Lt isOr inp m Y)

lemma mem_C {m : ℕ} {Y : Finset (Fin N)} :
    Y ∈ C ev z Tt Lt isOr inp m ↔ Y ⊆ Lt ∧ Cl ev z Tt Lt isOr inp m Y := by
  unfold C
  simp [Finset.mem_filter]

lemma step_merge (hS : Sem ev z Tt Lt isOr inp) (i : Fin len)
    (hm : Mrg ev z Tt Lt isOr inp i) :
    (C ev z Tt Lt isOr inp (i : ℕ)).card = 2 * (C ev z Tt Lt isOr inp ((i : ℕ) + 1)).card := by
  classical
  obtain ⟨hor, hz, w1, w2, hc, r, hr, r', hr', e1, e2, X0, hrX, hr'X, hX0⟩ := hm
  have m1 : w1 ∈ inp i := by rw [hc]; simp
  have m2 : w2 ∈ inp i := by rw [hc]; simp
  have key : ∀ Y, Cl ev z Tt Lt isOr inp (i : ℕ) Y →
      (Cl ev z Tt Lt isOr inp ((i : ℕ) + 1) Y ↔ (r ∈ Y ↔ r' ∈ Y)) := by
    intro Y hY
    constructor
    · intro h
      exact h i (by omega) hor hz w1 w2 hc r hr r' hr' (Or.inl e1) (Or.inr e2)
    · intro hrr j hj hor' hz' c1 c2 hc' s hs s' hs' hhs hhs'
      by_cases hji : (j : ℕ) < (i : ℕ)
      · exact hY j hji hor' hz' c1 c2 hc' s hs s' hs' hhs hhs'
      · have hjeq : j = i := Fin.ext (by omega)
        subst hjeq
        rw [hc] at hc'
        obtain ⟨rfl, rfl⟩ : w1 = c1 ∧ w2 = c2 := by simpa using hc'
        have S1 := side hS j hor hz w1 m1 Y hY
        have S2 := side hS j hor hz w2 m2 Y hY
        have A : ∀ u ∈ Lt, (ev w1 (Tt u) = true ∨ ev w2 (Tt u) = true) → (u ∈ Y ↔ r ∈ Y) := by
          intro u hu h
          rcases h with h | h
          · exact S1 u hu r hr h e1
          · exact (S2 u hu r' hr' h e2).trans hrr.symm
        exact (A s hs hhs).trans (A s' hs' hhs').symm
  have hZ : Cl ev z Tt Lt isOr inp (i : ℕ) (X0 ∩ Lt) := Cl_inter hX0
  have hrZ : r ∈ X0 ∩ Lt := Finset.mem_inter.mpr ⟨hrX, hr⟩
  have hr'Z : r' ∉ X0 ∩ Lt := fun h => hr'X (Finset.mem_inter.mp h).1
  have hsub : X0 ∩ Lt ⊆ Lt := Finset.inter_subset_right
  have hfilt : C ev z Tt Lt isOr inp ((i : ℕ) + 1) =
      (C ev z Tt Lt isOr inp (i : ℕ)).filter (fun Y => (r ∈ Y ↔ r' ∈ Y)) := by
    ext Y
    rw [Finset.mem_filter, mem_C, mem_C]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : Cl ev z Tt Lt isOr inp (i : ℕ) Y := Cl_mono (Nat.le_succ _) h2
      exact ⟨⟨h1, h3⟩, (key Y h3).1 h2⟩
    · rintro ⟨⟨h1, h3⟩, h4⟩
      exact ⟨h1, (key Y h3).2 h4⟩
  have hbij : ((C ev z Tt Lt isOr inp (i : ℕ)).filter (fun Y => (r ∈ Y ↔ r' ∈ Y))).card =
      ((C ev z Tt Lt isOr inp (i : ℕ)).filter (fun Y => ¬ (r ∈ Y ↔ r' ∈ Y))).card := by
    refine Finset.card_nbij' (fun Y => symmDiff Y (X0 ∩ Lt)) (fun Y => symmDiff Y (X0 ∩ Lt))
      ?_ ?_ ?_ ?_
    · intro Y hYm
      have hYm' := Finset.mem_filter.mp (Finset.mem_coe.mp hYm)
      obtain ⟨hY1, hY2⟩ := mem_C.mp hYm'.1
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨mem_C.mpr ⟨?_, Cl_symmDiff hY2 hZ⟩, ?_⟩)
      · exact Finset.symmDiff_subset_union.trans (Finset.union_subset hY1 hsub)
      · have := hYm'.2
        simp only [Finset.mem_symmDiff]
        tauto
    · intro Y hYm
      have hYm' := Finset.mem_filter.mp (Finset.mem_coe.mp hYm)
      obtain ⟨hY1, hY2⟩ := mem_C.mp hYm'.1
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨mem_C.mpr ⟨?_, Cl_symmDiff hY2 hZ⟩, ?_⟩)
      · exact Finset.symmDiff_subset_union.trans (Finset.union_subset hY1 hsub)
      · have := hYm'.2
        simp only [Finset.mem_symmDiff]
        tauto
    · intro Y _
      exact symmDiff_symmDiff_cancel_right _ _
    · intro Y _
      exact symmDiff_symmDiff_cancel_right _ _
  have hsum := Finset.card_filter_add_card_filter_not (s := C ev z Tt Lt isOr inp (i : ℕ))
    (fun Y => (r ∈ Y ↔ r' ∈ Y))
  rw [hfilt]
  omega

lemma count (hS : Sem ev z Tt Lt isOr inp) (I : Finset (Fin len))
    (hI : ∀ g, g ∈ I ↔ Mrg ev z Tt Lt isOr inp g) : ∀ m : ℕ, m ≤ len →
    (C ev z Tt Lt isOr inp m).card * 2 ^ (I.filter (fun g : Fin len => (g : ℕ) < m)).card =
      (C ev z Tt Lt isOr inp 0).card := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    by_cases hg : (⟨m, hm⟩ : Fin len) ∈ I
    · have hf : I.filter (fun g : Fin len => (g : ℕ) < m + 1) =
          insert (⟨m, hm⟩ : Fin len) (I.filter (fun g : Fin len => (g : ℕ) < m)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hlt⟩
          by_cases hxm : (x : ℕ) = m
          · exact Or.inl (Fin.ext hxm)
          · exact Or.inr ⟨hx, by omega⟩
        · rintro (rfl | ⟨hx, hlt⟩)
          · exact ⟨hg, Nat.lt_succ_self _⟩
          · exact ⟨hx, by omega⟩
      have hnot : (⟨m, hm⟩ : Fin len) ∉ I.filter (fun g : Fin len => (g : ℕ) < m) := by
        simp
      have hstep := step_merge hS ⟨m, hm⟩ ((hI _).1 hg)
      simp only at hstep
      rw [hf, Finset.card_insert_of_notMem hnot, pow_succ, ← ih', hstep]
      ring
    · have hf : I.filter (fun g : Fin len => (g : ℕ) < m + 1) = I.filter (fun g : Fin len => (g : ℕ) < m) := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx, hlt⟩
          refine ⟨hx, ?_⟩
          by_contra hge
          have hxm : x = ⟨m, hm⟩ := Fin.ext (by simp only; omega)
          rw [hxm] at hx
          exact hg hx
        · rintro ⟨hx, hlt⟩
          exact ⟨hx, by omega⟩
      have hC : C ev z Tt Lt isOr inp (m + 1) = C ev z Tt Lt isOr inp m := by
        ext Y
        rw [mem_C, mem_C]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, Cl_mono (Nat.le_succ _) h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, step_not hS ⟨m, hm⟩ (fun h => hg ((hI _).2 h)) Y h2⟩
      rw [hf, hC]
      exact ih'

lemma card_C0 : (C ev z Tt Lt isOr inp 0).card = 2 ^ Lt.card := by
  have h : C ev z Tt Lt isOr inp 0 = Lt.powerset := by
    ext Y
    rw [mem_C, Finset.mem_powerset]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [h, Finset.card_powerset]

lemma card_Clen (hS : Sem ev z Tt Lt isOr inp) (ot : ℕ) (hoz : ev ot z = false)
    (hoT : ∀ p ∈ Lt, ev ot (Tt p) = true) (hne : Lt.Nonempty) :
    (C ev z Tt Lt isOr inp len).card = 2 := by
  have h : C ev z Tt Lt isOr inp len = {∅, Lt} := by
    ext Y
    rw [mem_C, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      have hall : ∀ a ∈ Lt, ∀ b ∈ Lt, (a ∈ Y ↔ b ∈ Y) := fun a ha b hb =>
        S hS ot hoz a ha b hb (hoT a ha) (hoT b hb) Y (Cl_of_len h2)
      by_cases hY : Y.Nonempty
      · obtain ⟨a, ha⟩ := hY
        right
        exact Finset.Subset.antisymm h1 (fun b hb => (hall a (h1 ha) b hb).1 ha)
      · left
        exact Finset.not_nonempty_iff_eq_empty.mp hY
    · rintro (rfl | rfl)
      · exact ⟨Finset.empty_subset _, fun i _ _ _ c1 c2 _ s _ s' _ _ _ => by simp⟩
      · exact ⟨Finset.Subset.refl _, fun i _ _ _ c1 c2 _ s hs s' hs' _ _ =>
          ⟨fun _ => hs', fun _ => hs⟩⟩
  rw [h, Finset.card_pair_eq_two_iff]
  exact fun h => hne.ne_empty h.symm

lemma final_abs (hS : Sem ev z Tt Lt isOr inp) (ot : ℕ) (hoz : ev ot z = false)
    (hoT : ∀ p ∈ Lt, ev ot (Tt p) = true) (q : ℕ) (hq : Lt.card = q + 1)
    (I : Finset (Fin len)) (hI : ∀ g, g ∈ I ↔ Mrg ev z Tt Lt isOr inp g) : I.card = q := by
  have hne : Lt.Nonempty := by
    rw [← Finset.card_pos, hq]
    omega
  have h := count hS I hI len (le_refl _)
  rw [card_C0, card_Clen hS ot hoz hoT hne, hq] at h
  have hf : I.filter (fun g : Fin len => (g : ℕ) < len) = I :=
    Finset.filter_true_of_mem (fun g _ => g.2)
  rw [hf] at h
  have h2 : 2 ^ (I.card + 1) = 2 ^ (q + 1) := by
    rw [pow_succ, mul_comm]
    exact h
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

end abs

lemma sem_of (N : ℕ) (Lt : Finset (Fin N)) (Tt : Fin N → Fin N → Bool)
    (hTt : ∀ a ∈ Lt, ∀ v ∈ Lt, Tt a v = true → a = v)
    (gates : List Gate)
    (hops : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hpos : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = Circuit.eval ⟨gates, w⟩ (List.ofFn x)) :
    Sem ev (fun v : Fin N => decide (v ∉ Lt)) Tt Lt
      (fun i : Fin gates.length => (gates.get i).op = GateOp.or)
      (fun i : Fin gates.length => (gates.get i).inputs) := by
  have hin : ∀ (v : Fin N) (x : Fin N → Bool), ev (v : ℕ) x = x v := by
    intro v x
    rw [hev, eval_eq, val_input _ _ _ (by rw [List.length_ofFn]; exact v.2), getD_ofFn _ _ v.2]
  have hgate : ∀ (i : Fin gates.length) (x : Fin N → Bool), ev (N + (i : ℕ)) x =
      (gates.get i).op.eval ((gates.get i).inputs.map (fun c => ev c x)) := by
    intro i x
    have h := val_gate gates (List.ofFn x) i i.2 (by
      intro a ha
      rw [List.length_ofFn]
      exact hwf i a ha)
    rw [List.length_ofFn] at h
    rw [hev, eval_eq, h]
    have hfun : (fun c => ev c x) = val gates (List.ofFn x) := by
      funext c
      rw [hev, eval_eq]
    rw [hfun]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hz a ha hT
    rw [hin] at hz hT
    have hv : v ∈ Lt := by simpa using hz
    exact hTt a ha v hv hT
  · intro w hw x
    rw [hev, eval_eq]
    exact val_big _ _ _ (by rw [List.length_ofFn]; exact hw)
  · intro i
    rcases (hops (gates.get i) (List.get_mem _ _)).1 with hand | hor
    · left
      refine ⟨?_, ?_, ?_⟩
      · show ¬ (gates.get i).op = GateOp.or
        rw [hand]
        intro h
        cases h
      · intro x hx c hc
        rw [hgate, hand] at hx
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂] at hx
        simpa using hx c hc
      · intro x hx
        rw [hgate, hand] at hx
        simp only [GateOp.eval, List.all_eq_false, List.mem_map] at hx
        obtain ⟨b, ⟨c, hc, rfl⟩, hb⟩ := hx
        exact ⟨c, hc, by simpa using hb⟩
    · right
      refine ⟨hor, ?_⟩
      intro x
      rw [hgate, hor]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map]
      constructor
      · rintro ⟨b, ⟨c, hc, rfl⟩, hb⟩
        exact ⟨c, hc, by simpa using hb⟩
      · rintro ⟨c, hc, hb⟩
        exact ⟨ev c x, ⟨c, hc, rfl⟩, by simpa using hb⟩
  · intro i
    refine ⟨hwf i, ?_⟩
    have h1 := hpos i
    have h2 := (hops (gates.get i) (List.get_mem _ _)).2
    rcases hl : (gates.get i).inputs with _ | ⟨c, _ | ⟨c2, _ | ⟨c3, tl⟩⟩⟩
    · rw [hl] at h1
      simp at h1
    · exact Or.inl ⟨c, hl⟩
    · exact Or.inr ⟨c, c2, hl⟩
    · rw [hl] at h2
      simp at h2

end PEqualNP.Outside.L_meta_1635

theorem PEqualNP.Outside.L_meta_1635 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) →
    ∀ Mg : Fin N → Fin gates.length → Prop,
    (∀ (t : Fin N) (g : Fin gates.length), Mg t g ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L t, ∃ r' ∈ L t, ev w1 (T t r) = true ∧ ev w2 (T t r') = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (ev c1 (T t s) = true ∨ ev c2 (T t s) = true) → (ev c1 (T t s') = true ∨ ev c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)))) →
    ∀ t : Fin N,
      (∀ g : Fin gates.length, ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false → ∀ a ∈ L t, ∀ b ∈ L t, ev (N + (g : ℕ)) (T t a) = true → ev (N + (g : ℕ)) (T t b) = true →
        ∀ X : Finset (Fin N), (∀ i : Fin gates.length, i ≤ g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (ev c1 (T t s) = true ∨ ev c2 (T t s) = true) → (ev c1 (T t s') = true ∨ ev c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)) → (a ∈ X ↔ b ∈ X)) ∧
      ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ I ↔ Mg t g) → I.card = q := by
  intro q N L i0 p0 p1 _ _ hcard hmeet _ hp01 hp0 hp1 T hT gates hops hpos hwf ev hev o ho Mg hMg t
  have hTt : ∀ a ∈ L t, ∀ v ∈ L t, T t a v = true → a = v := by
    intro a _ v hv h
    rcases (hT t a v).1 h with h | ⟨h1, _, h3⟩ | ⟨_, h2, _, h4⟩ | ⟨_, _, _, _, h5⟩
    · exact h.symm
    · rw [h3] at hv
      exact absurd hv h1
    · rw [h4] at hv
      exact absurd hv h2
    · exact absurd hv h5
  have hS := PEqualNP.Outside.L_meta_1635.sem_of N (L t) (T t) hTt gates hops hpos hwf ev hev
  have hti0 : p0 ∈ L t → p1 ∈ L t → t = i0 := by
    intro h0 h1
    by_contra hne
    have hc := hmeet t i0 hne
    have hlt : 1 < (L t ∩ L i0).card :=
      Finset.one_lt_card.mpr ⟨p0, Finset.mem_inter.mpr ⟨h0, hp0⟩, p1,
        Finset.mem_inter.mpr ⟨h1, hp1⟩, hp01⟩
    omega
  have hoz : ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false := by
    rw [ho t]
    · simp
    · by_cases h0 : p0 ∈ L t
      · by_cases h1 : p1 ∈ L t
        · right
          right
          intro u hu
          rw [hti0 h0 h1]
          simpa using hu
        · right
          left
          simpa using h1
      · left
        simpa using h0
  have hoT : ∀ p ∈ L t, ev (o t) (T t p) = true := by
    intro p hp
    rw [ho t]
    · have : T t p p = true := (hT t p p).2 (Or.inl rfl)
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, this⟩
    · by_cases h0 : p0 ∈ L t
      · by_cases h1 : p1 ∈ L t
        · by_cases e0 : p = p0
          · left
            exact (hT t p p0).2 (Or.inl e0.symm)
          · by_cases e1 : p = p1
            · right
              left
              exact (hT t p p1).2 (Or.inl e1.symm)
            · right
              right
              intro u hu
              rw [← hti0 h0 h1] at hu
              exact (hT t p u).2 (Or.inr (Or.inr (Or.inr ⟨h0, h1, e0, e1, hu⟩)))
        · by_cases e0 : p = p0
          · left
            exact (hT t p p0).2 (Or.inl e0.symm)
          · right
            left
            exact (hT t p p1).2 (Or.inr (Or.inr (Or.inl ⟨h0, h1, e0, rfl⟩)))
      · by_cases e1 : p = p1
        · right
          left
          exact (hT t p p1).2 (Or.inl e1.symm)
        · left
          exact (hT t p p0).2 (Or.inr (Or.inl ⟨h0, e1, rfl⟩))
  refine ⟨?_, ?_⟩
  · intro g hz a ha b hb hTa hTb X hX
    refine PEqualNP.Outside.L_meta_1635.S hS (N + (g : ℕ)) hz a ha b hb hTa hTb X ?_
    intro i hi
    exact hX i (Fin.le_def.mpr (by omega))
  · intro I hI
    refine PEqualNP.Outside.L_meta_1635.final_abs hS (o t) hoz hoT q (hcard t) I ?_
    intro g
    exact (hI g).trans (hMg t g)
