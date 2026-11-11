import Mathlib

/-! # Cycles impairs de la bataille, perdante en premier

Théorème 2, Lemme 3 et Corollaire 4 du PDF. Les définitions de l'état,
du tour et du chemin reprennent le modèle du fichier du sens facile.
-/
namespace A400868.OddCycles
abbrev State (α : Type*) := List α × List α

def step {α : Type*} [LinearOrder α] (s : State α) : State α :=
  match s with
  | (x::xs,y::ys) => if x< y then (xs,ys++[x,y]) else (xs++[y,x],ys)
  | _ => s
def run {α : Type*} [LinearOrder α] : ℕ → State α → State α
  | 0,s => s
  | k+1,s => run k (step s)
inductive Turn {α : Type*} [LT α] : State α → State α → Prop
  | left {x y : α} {xs ys : List α} (h : y< x) : Turn (x::xs,y::ys) (xs++[y,x],ys)
  | right {x y : α} {xs ys : List α} (h : x< y) : Turn (x::xs,y::ys) (xs,ys++[x,y])
inductive Path {α : Type*} [LT α] : ℕ → State α → State α → Prop
  | zero (s) : Path 0 s s
  | cons {k s t u} : Turn s t → Path k t u → Path (k+1) s u

lemma turn_step {α : Type*} [LinearOrder α] {s t : State α} (h : Turn s t) : step s=t := by
  cases h with
  | left h => simp [step,not_lt_of_gt h]
  | right h => simp [step,h]
lemma path_trans {α : Type*} [LT α] {k l : ℕ} {s t u : State α}
    (h : Path k s t) (g : Path l t u) : Path (k+l) s u := by
  induction h with
  | zero => simpa using g
  | cons ht hp ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ht (ih g)
lemma loop_repeat {α : Type*} [LT α] {k : ℕ} {s : State α} (h : Path k s s) (r : ℕ) : Path (r*k) s s := by
  induction r with
  | zero => simpa using Path.zero s
  | succ r ih => simpa [Nat.succ_mul] using path_trans ih h
variable {α : Type*} [LinearOrder α]

/-- true marque une carte gagnante lors de son dernier tour. -/
abbrev MarkedState (α : Type*) := State (α × Bool)

def erase (s : MarkedState α) : State α :=
  (s.1.map Prod.fst, s.2.map Prod.fst)

def mark : List α → List (α × Bool)
  | [] => []
  | x::xs => (x, decide (xs.length % 2 = 0)) :: mark xs

def markState (s : State α) : MarkedState α := (mark s.1, mark s.2)

inductive MarkedTurn : MarkedState α → MarkedState α → Prop
  | left {x y : α} {bx by' : Bool} {xs ys : List (α × Bool)} (h : y < x) :
      MarkedTurn ((x,bx)::xs,(y,by')::ys) (xs++[(y,false),(x,true)],ys)
  | right {x y : α} {bx by' : Bool} {xs ys : List (α × Bool)} (h : x < y) :
      MarkedTurn ((x,bx)::xs,(y,by')::ys) (xs,ys++[(x,false),(y,true)])

inductive MarkedPath : ℕ → MarkedState α → MarkedState α → Prop
  | zero (s : MarkedState α) : MarkedPath 0 s s
  | cons {k s t u} : MarkedTurn s t → MarkedPath k t u → MarkedPath (k+1) s u

/-- Un paquet complet est lu du sommet vers le fond. -/
inductive Complete : List (α × Bool) → Prop
  | nil : Complete []
  | cons {l w : α} {rest} : l < w → Complete rest →
      Complete ((l,false)::(w,true)::rest)

/-- Au sommet, la gagnante d'une ancienne paire peut être seule. -/
inductive Captured : List (α × Bool) → Prop
  | even {L} : Complete L → Captured L
  | odd (w : α) {L} : Complete L → Captured ((w,true)::L)

private theorem Complete.appendPair {L : List (α × Bool)} (h : Complete L)
    {l w : α} (hlt : l < w) : Complete (L++[(l,false),(w,true)]) := by
  induction h with
  | nil => exact Complete.cons hlt Complete.nil
  | cons h₁ h₂ ih => exact Complete.cons h₁ ih

private theorem Captured.appendPair {L : List (α × Bool)} (h : Captured L)
    {l w : α} (hlt : l < w) : Captured (L++[(l,false),(w,true)]) := by
  cases h with
  | even h => exact .even (h.appendPair hlt)
  | odd w h => exact .odd w (h.appendPair hlt)

private theorem Captured.tail {L : List (α × Bool)} (h : Captured L) : Captured L.tail := by
  cases h with
  | even h =>
    cases h with
    | nil => exact .even .nil
    | cons hlt hrest => exact .odd _ hrest
  | odd w h => exact .even h

private theorem Complete.evenLength {L : List (α × Bool)} (h : Complete L) :
    L.length % 2 = 0 := by
  induction h <;> simp only [List.length_nil, List.length_cons] at *; omega

private theorem Complete.canonical {L : List (α × Bool)} (h : Complete L) :
    mark (L.map Prod.fst) = L := by
  induction h with
  | nil => rfl
  | @cons l w rest hlt hRest ih =>
    have he := hRest.evenLength
    have ho : (rest.length + 1) % 2 ≠ 0 := by omega
    simp [mark, List.length_map, he, ho, ih]

private theorem Captured.canonical {L : List (α × Bool)} (h : Captured L) :
    mark (L.map Prod.fst) = L := by
  cases h with
  | even h => exact h.canonical
  | odd w h => simp [mark, h.evenLength, h.canonical]

omit [LinearOrder α] in
@[simp] theorem erase_markState (s : State α) : erase (markState s) = s := by
  have he (L : List α) : (mark L).map Prod.fst = L := by
    induction L with
    | nil => rfl
    | cons x xs ih => simp [mark, ih]
  simp [erase, markState, he]

omit [LinearOrder α] in
private theorem mark_append_pair (xs : List α) (l w : α) :
    mark (xs++[l,w]) = mark xs ++ [(l,false),(w,true)] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : (xs.length + 2) % 2 = xs.length % 2 := by omega
    simp [mark, List.length_append, h, ih]

theorem mark_turn {s t : State α} (h : Turn s t) :
    MarkedTurn (markState s) (markState t) := by
  cases h with
  | left h => simpa only [markState, mark, mark_append_pair] using (MarkedTurn.left h)
  | right h => simpa only [markState, mark, mark_append_pair] using (MarkedTurn.right h)

private theorem lift_turn {s t : State α} (h : Turn s t) (S : MarkedState α)
    (he : erase S = s) : ∃ T, erase T = t ∧ MarkedTurn S T := by
  rcases S with ⟨xs,ys⟩
  cases h with
  | left h =>
    cases xs with
    | nil => simp [erase] at he
    | cons x xs =>
      cases ys with
      | nil => simp [erase] at he
      | cons y ys =>
        simp only [erase, List.map_cons, Prod.mk.injEq, List.cons.injEq] at he
        have ht : y.1 < x.1 := by rw [he.1.1, he.2.1]; exact h
        refine ⟨(xs++[(y.1,false),(x.1,true)],ys), ?_, MarkedTurn.left ht⟩
        simp [erase, he.1.1, he.1.2, he.2.1, he.2.2]
  | right h =>
    cases xs with
    | nil => simp [erase] at he
    | cons x xs =>
      cases ys with
      | nil => simp [erase] at he
      | cons y ys =>
        simp only [erase, List.map_cons, Prod.mk.injEq, List.cons.injEq] at he
        have ht : x.1 < y.1 := by rw [he.1.1, he.2.1]; exact h
        refine ⟨(xs,ys++[(x.1,false),(y.1,true)]), ?_, MarkedTurn.right ht⟩
        simp [erase, he.1.1, he.1.2, he.2.1, he.2.2]

theorem lift_path {k : ℕ} {s t : State α} (h : Path k s t) (S : MarkedState α)
    (he : erase S = s) : ∃ T, erase T = t ∧ MarkedPath k S T := by
  induction h generalizing S with
  | zero => exact ⟨S, he, .zero _⟩
  | cons ht _ ih =>
    obtain ⟨S',he',hs⟩ := lift_turn ht S he
    obtain ⟨T,ht',hp⟩ := ih S' he'
    exact ⟨T,ht',.cons hs hp⟩

/-- Les cartes initiales encore en attente forment un préfixe de longueur bornée. -/
private def MatureIn (b : ℕ) (L : List (α × Bool)) : Prop :=
  ∃ U V, L = U++V ∧ U.length ≤ b ∧ Captured V

private theorem MatureIn.tail {b : ℕ} {L : List (α × Bool)} (h : MatureIn b L) :
    MatureIn (b-1) L.tail := by
  obtain ⟨U,V,rfl,hU,hV⟩ := h
  cases U with
  | nil => exact ⟨[],V.tail,rfl,by simp,hV.tail⟩
  | cons x U =>
    exact ⟨U,V,rfl,by simp only [List.length_cons] at hU; omega,hV⟩

private theorem MatureIn.appendPair {b : ℕ} {L : List (α × Bool)} (h : MatureIn b L)
    {l w : α} (hlt : l < w) : MatureIn b (L++[(l,false),(w,true)]) := by
  obtain ⟨U,V,rfl,hU,hV⟩ := h
  exact ⟨U,_,List.append_assoc ..,hU,hV.appendPair hlt⟩

private theorem MarkedPath.mature {k b : ℕ} {s t : MarkedState α} (h : MarkedPath k s t)
    (h₁ : MatureIn b s.1) (h₂ : MatureIn b s.2) :
    MatureIn (b-k) t.1 ∧ MatureIn (b-k) t.2 := by
  induction h generalizing b with
  | zero => simpa using And.intro h₁ h₂
  | cons ht _ ih =>
    cases ht with
    | left h =>
      simpa only [Nat.sub_sub, Nat.add_comm] using ih (h₁.tail.appendPair h) h₂.tail
    | right h =>
      simpa only [Nat.sub_sub, Nat.add_comm] using ih h₁.tail (h₂.tail.appendPair h)

private theorem MatureIn.zero {L : List (α × Bool)} (h : MatureIn 0 L) : Captured L := by
  obtain ⟨U,V,rfl,hU,hV⟩ := h
  have hU' : U = [] := List.length_eq_zero_iff.mp (by omega)
  simpa [hU'] using hV

def Cycle (s : State α) : Prop := ∃ k, 0 < k ∧ Path k s s

/-- Après assez de tours, les marques sont déterminées par les captures,
quelles qu'aient été les marques initiales. -/
theorem fifo_flush {k : ℕ} {s t : MarkedState α} (h : MarkedPath k s t)
    (h₁ : s.1.length ≤ k) (h₂ : s.2.length ≤ k) :
    Captured t.1 ∧ Captured t.2 ∧ t = markState (erase t) := by
  have hm := h.mature (b := k)
    ⟨s.1,[],by simp,h₁,.even .nil⟩ ⟨s.2,[],by simp,h₂,.even .nil⟩
  have hc₁ := MatureIn.zero (by simpa using hm.1)
  have hc₂ := MatureIn.zero (by simpa using hm.2)
  exact ⟨hc₁,hc₂,Prod.ext hc₁.canonical.symm hc₂.canonical.symm⟩

/-- Lemme 3. En remontant assez loin sur le cycle, on retrouve les marques
canoniques par des tours qui enregistrent les victoires et défaites. -/
theorem cycle_pairs {s : State α} (hc : Cycle s) (S : MarkedState α) (he : erase S = s) :
    ∃ k, 0 < k ∧ MarkedPath k S (markState s) ∧
      Captured (markState s).1 ∧ Captured (markState s).2 := by
  obtain ⟨d,hd,h⟩ := hc
  let b := S.1.length + S.2.length + 1
  have hk : b ≤ b*d := by
    simpa using Nat.mul_le_mul_left b (show 1 ≤ d by omega)
  obtain ⟨T,he',hT⟩ := lift_path (loop_repeat h b) S he
  have hb₁ : S.1.length ≤ b := by dsimp [b]; omega
  have hb₂ : S.2.length ≤ b := by dsimp [b]; omega
  have hb : 0 < b := by dsimp [b]; omega
  obtain ⟨h₁,h₂,hm⟩ := fifo_flush hT (hb₁.trans hk) (hb₂.trans hk)
  rw [he'] at hm
  subst T
  exact ⟨b*d,Nat.mul_pos hb hd,hT,h₁,h₂⟩


def size (s : State α) : ℕ := s.1.length + s.2.length

abbrev HeadW (L : List α) : Prop := L.length % 2 = 1

omit [LinearOrder α] in
theorem marked_head {x : α} {xs : List α} :
    (mark (x::xs)).head? = some (x, decide (HeadW (x::xs))) := by
  have h : xs.length % 2 = 0 ↔ HeadW (x::xs) := by
    simp only [HeadW, List.length_cons]
    omega
  simp [mark, h]

omit [LinearOrder α] in
/-- Corollaire 4. Pour des paquets non vides, il s'agit des rôles des têtes. -/
theorem phase (s : State α) :
    (HeadW s.1 ↔ HeadW s.2) ↔ size s % 2 = 0 := by
  unfold HeadW size
  omega

private theorem turn_size {s t : State α} (h : Turn s t) : size t = size s := by
  cases h <;> simp [size] <;> omega

private theorem turn_return {s t : State α} (hc : Cycle s) (h : Turn s t) :
    ∃ k, Path k t s := by
  obtain ⟨k,hk,hp⟩ := hc
  cases hp with
  | zero => omega
  | cons ht hp =>
    have he := (turn_step h).symm.trans (turn_step ht)
    subst t
    exact ⟨_,hp⟩

theorem cycle_next {s t : State α} (hc : Cycle s) (h : Turn s t) : Cycle t := by
  obtain ⟨k,hp⟩ := turn_return hc h
  exact ⟨k+1,by omega,path_trans hp (.cons h (.zero _))⟩

theorem cycle_has_turn {s : State α} (hc : Cycle s) : ∃ t, Turn s t := by
  obtain ⟨k,hk,hp⟩ := hc
  cases hp with
  | zero => omega
  | cons h _ => exact ⟨_,h⟩

def WWin : State α → Prop
  | (x::xs,y::ys) => (y < x ∧ HeadW (x::xs)) ∨ (x < y ∧ HeadW (y::ys))
  | _ => False

private def countLoss (θ : α) (L : List (α × Bool)) : ℕ :=
  L.countP (fun a => !a.2 && decide (θ < a.1))

def potential (θ : α) (s : State α) : ℕ :=
  countLoss θ (mark s.1) + countLoss θ (mark s.2)

omit [LinearOrder α] in
private theorem opposite {x y : α} {xs ys : List α}
    (h : size (x::xs,y::ys) % 2 = 1) :
    xs.length % 2 = 0 ↔ ys.length % 2 ≠ 0 := by
  simp only [size, List.length_cons] at h
  omega

private theorem turn_potential_le (θ : α) {s t : State α} (h : Turn s t)
    (ho : size s % 2 = 1) : potential θ t ≤ potential θ s := by
  cases h with
  | @left x y xs ys hlt =>
    have hp := opposite ho
    by_cases hx : xs.length % 2 = 0
    · have hy := hp.1 hx
      simp [potential, countLoss, mark, mark_append_pair, List.countP_append, List.countP_cons, hx, hy]; omega
    · have hy : ys.length % 2 = 0 := by by_contra hn; exact hx (hp.2 hn)
      by_cases hy' : θ < y
      · have hx' := hy'.trans hlt
        simp [potential, countLoss, mark, mark_append_pair, List.countP_append, hx, hy, hy', hx']
      · simp [potential, countLoss, mark, mark_append_pair, List.countP_append, List.countP_cons, hx, hy, hy']
  | @right x y xs ys hlt =>
    have hp := opposite ho
    by_cases hx : xs.length % 2 = 0
    · have hy := hp.1 hx
      by_cases hx' : θ < x
      · have hy' := hx'.trans hlt
        simp [potential, countLoss, mark, mark_append_pair, List.countP_append, hx, hy, hx', hy']
      · simp [potential, countLoss, mark, mark_append_pair, List.countP_append, List.countP_cons, hx, hy, hx']
    · have hy : ys.length % 2 = 0 := by by_contra hn; exact hx (hp.2 hn)
      simp [potential, countLoss, mark, mark_append_pair, List.countP_append, List.countP_cons, hx, hy]; omega

private theorem path_potential_le (θ : α) {s t : State α} {k : ℕ} (h : Path k s t)
    (ho : size s % 2 = 1) : potential θ t ≤ potential θ s := by
  induction h with
  | zero => exact le_rfl
  | cons ht _ ih =>
    exact (ih (by rwa [turn_size ht])).trans (turn_potential_le θ ht ho)

private theorem upset_decreases {s t : State α} (h : Turn s t)
    (ho : size s % 2 = 1) (hb : ¬ WWin s) :
    ∃ θ, potential θ t < potential θ s := by
  cases h with
  | @left x y xs ys hlt =>
    have hp := opposite ho
    have hx : xs.length % 2 ≠ 0 := by
      intro hx
      exact hb (Or.inl ⟨hlt, by simp [HeadW]; omega⟩)
    have hy : ys.length % 2 = 0 := by by_contra hn; exact hx (hp.2 hn)
    refine ⟨y,?_⟩
    simp [potential, countLoss, mark, mark_append_pair, List.countP_append, hx, hy, hlt]
  | @right x y xs ys hlt =>
    have hp := opposite ho
    have hy : ys.length % 2 ≠ 0 := by
      intro hy
      exact hb (Or.inr ⟨hlt, by simp [HeadW]; omega⟩)
    have hx := hp.2 hy
    refine ⟨x,?_⟩
    simp [potential, countLoss, mark, mark_append_pair, List.countP_append, hx, hy, hlt]

/-- Théorème 2. Dans un cycle impair, la tête W gagne à chaque tour. -/
theorem theorem2 {s : State α} (hc : Cycle s) (ho : size s % 2 = 1) :
    WWin s := by
  obtain ⟨t,h⟩ := cycle_has_turn hc
  by_contra hb
  obtain ⟨θ,hlt⟩ := upset_decreases h ho hb
  obtain ⟨k,hp⟩ := turn_return hc h
  exact (not_lt_of_ge (path_potential_le θ hp (by rwa [turn_size h]))) hlt

def rolePile (b : Bool) (L : List (α × Bool)) : List α :=
  L.filterMap fun a => if a.2 = b then some a.1 else none

def cardsOf (b : Bool) (s : State α) : Multiset α :=
  (rolePile b (mark s.1) : Multiset α) + (rolePile b (mark s.2) : Multiset α)

def WinnerLeft : State α → Prop
  | (x::_,y::_) => y < x
  | _ => False

private theorem winner_left_parity {s t : State α} (h : Turn s t)
    (ho : size s % 2 = 1) (hw : WWin s) : WinnerLeft s ↔ HeadW s.1 := by
  cases h with
  | @left x y xs ys h =>
    simp only [WWin, h, not_lt_of_gt h, false_and, or_false, true_and] at hw
    exact ⟨fun _ => hw, fun _ => h⟩
  | @right x y xs ys h =>
    have hp := opposite ho
    simp only [WWin, h, not_lt_of_gt h, false_and, false_or, true_and] at hw
    have hy : ys.length % 2 = 0 := by
      simp only [HeadW, List.length_cons] at hw
      omega
    have hx : ¬ HeadW (x::xs) := by
      intro h'
      simp only [HeadW, List.length_cons] at h'
      exact (hp.1 (by omega)) hy
    simp [WinnerLeft, not_lt_of_gt h, hx]

theorem winners_alternate {s t : State α} (hc : Cycle s) (ho : size s % 2 = 1)
    (h : Turn s t) : WinnerLeft t ↔ ¬ WinnerLeft s := by
  have hc' := cycle_next hc h
  have ho' : size t % 2 = 1 := by rwa [turn_size h]
  obtain ⟨u,ht⟩ := cycle_has_turn hc'
  rw [winner_left_parity ht ho' (theorem2 hc' ho'),
    winner_left_parity h ho (theorem2 hc ho)]
  cases h <;> simp only [HeadW, List.length_append, List.length_cons, List.length_nil] <;> omega

private theorem roles_turn {s t : State α} (h : Turn s t)
    (ho : size s % 2 = 1) (hw : WWin s) (b : Bool) : cardsOf b t = cardsOf b s := by
  cases h with
  | @left x y xs ys h =>
    have hp := opposite ho
    simp only [WWin, h, not_lt_of_gt h, false_and, or_false, true_and,
      HeadW, List.length_cons] at hw
    have hx : xs.length % 2 = 0 := by omega
    have hy := hp.1 hx
    cases b <;> simp [cardsOf, rolePile, mark, mark_append_pair, List.filterMap_append,
      hx, hy]
  | @right x y xs ys h =>
    have hp := opposite ho
    simp only [WWin, h, not_lt_of_gt h, false_and, false_or, true_and,
      HeadW, List.length_cons] at hw
    have hy : ys.length % 2 = 0 := by omega
    have hx : xs.length % 2 ≠ 0 := fun h => (hp.1 h) hy
    cases b <;> simp [cardsOf, rolePile, mark, mark_append_pair, List.filterMap_append,
      hx, hy]
    · simpa only [List.append_assoc, List.singleton_append] using
        (List.perm_append_comm (l₁ := _ ++ _) (l₂ := [x]))
    · exact List.Perm.append_left _ (List.perm_append_comm (l₂ := [y]))

omit [LinearOrder α] in
private theorem count_roles (L : List α) :
    (rolePile true (mark L)).length = (L.length+1)/2 ∧
    (rolePile false (mark L)).length = L.length/2 := by
  induction L with
  | nil => simp [rolePile, mark]
  | cons x xs ih =>
    by_cases hx : xs.length % 2 = 0
    · simp [rolePile, mark, hx] at ih ⊢
      omega
    · simp [rolePile, mark, hx] at ih ⊢
      omega

omit [LinearOrder α] in
theorem role_counts {s : State α} (ho : size s % 2 = 1) :
    (cardsOf true s).card = (size s+1)/2 ∧
    (cardsOf false s).card = (size s-1)/2 := by
  obtain ⟨h₁,h₂⟩ := count_roles s.1
  obtain ⟨h₃,h₄⟩ := count_roles s.2
  simp only [cardsOf, Multiset.card_add, Multiset.coe_card, h₁,h₂,h₃,h₄, size] at ho ⊢
  omega

private theorem run_last_step (k : ℕ) (s : State α) :
    run (k+1) s = step (run k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (step s)

theorem cycle_run {s : State α} (hc : Cycle s) (ho : size s % 2 = 1) (k : ℕ) :
    Cycle (run k s) ∧ size (run k s) % 2 = 1 ∧
      ∀ b, cardsOf b (run k s) = cardsOf b s := by
  induction k with
  | zero => exact ⟨hc,ho,fun _ => rfl⟩
  | succ k ih =>
    obtain ⟨hc',ho',hr⟩ := ih
    obtain ⟨t,ht⟩ := cycle_has_turn hc'
    rw [run_last_step, turn_step ht]
    exact ⟨cycle_next hc' ht,by rwa [turn_size ht],
      fun b => (roles_turn ht ho' (theorem2 hc' ho') b).trans (hr b)⟩

/-- Victoire de W à chaque tour, rôles constants et victoires alternées. -/
theorem odd_cycle_dynamics {s : State α} (hc : Cycle s) (ho : size s % 2 = 1) (k : ℕ) :
    WWin (run k s) ∧ (∀ b, cardsOf b (run k s) = cardsOf b s) ∧
      (WinnerLeft (run (k+1) s) ↔ ¬ WinnerLeft (run k s)) := by
  obtain ⟨hc',ho',hr⟩ := cycle_run hc ho k
  obtain ⟨t,ht⟩ := cycle_has_turn hc'
  rw [run_last_step, turn_step ht]
  exact ⟨theorem2 hc' ho', hr, winners_alternate hc' ho' ht⟩

/-- La gagnante et la perdante de ce tour, avec les marques héritées. -/
def WBeatsL (S : MarkedState α) : Prop :=
  ∃ w l : α, l < w ∧
    ((S.1.head? = some (w, true) ∧ S.2.head? = some (l, false)) ∨
     (S.2.head? = some (w, true) ∧ S.1.head? = some (l, false)))

/-- À chaque phase, les marques obtenues en rejouant le cycle
donnent une tête W strictement plus forte que la tête L. -/
theorem theorem2_marked {s : State α} (hc : Cycle s) (ho : size s % 2 = 1)
    (S : MarkedState α) (he : erase S = s) :
    ∃ k T, 0 < k ∧ MarkedPath k S T ∧ erase T = s ∧ WBeatsL T := by
  obtain ⟨k, hk, hpath, _, _⟩ := cycle_pairs hc S he
  refine ⟨k, markState s, hk, hpath, erase_markState s, ?_⟩
  have hw := theorem2 hc ho
  obtain ⟨t, ht⟩ := cycle_has_turn hc
  cases ht with
  | @left x y xs ys h =>
    have hp := opposite ho
    simp only [WWin, h, not_lt_of_gt h, false_and, or_false, true_and,
      HeadW, List.length_cons] at hw
    have hx : xs.length % 2 = 0 := by omega
    have hy := hp.1 hx
    exact ⟨x, y, h, Or.inl ⟨by simp [markState, mark, hx], by simp [markState, mark, hy]⟩⟩
  | @right x y xs ys h =>
    have hp := opposite ho
    simp only [WWin, h, not_lt_of_gt h, false_and, false_or, true_and,
      HeadW, List.length_cons] at hw
    have hy : ys.length % 2 = 0 := by omega
    have hx : xs.length % 2 ≠ 0 := fun hx => (hp.1 hx) hy
    exact ⟨y, x, h, Or.inr ⟨by simp [markState, mark, hy], by simp [markState, mark, hx]⟩⟩

#print axioms fifo_flush
#print axioms cycle_pairs
#print axioms phase
#print axioms theorem2
#print axioms theorem2_marked
#print axioms role_counts
#print axioms odd_cycle_dynamics

end A400868.OddCycles
