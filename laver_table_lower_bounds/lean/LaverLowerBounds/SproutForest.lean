import LaverLowerBounds.SproutDynamics

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

/-- A stack of two-level trees, with the first rank at the right-hand end. -/
def decorated (offset : Nat) (template : Column) : List Nat → Matrix
  | [] => []
  | k :: rest =>
      let earlier := decorated offset template rest
      earlier ++ [template] ++ List.replicate k [offset + earlier.length]

theorem decorated_translated (offset distance : Nat) (template : Column) (ranks : List Nat) :
    translated distance (decorated offset template ranks) =
      decorated (offset + distance) (template.map (fun p => p + distance)) ranks := by
  induction ranks with
  | nil => simp [decorated, translated]
  | cons k rest ih =>
      simp only [decorated, translated_append]
      rw [ih]
      have hlen := congrArg List.length ih
      rw [translated_length] at hlen
      simp only [translated, List.map_cons, List.map_nil, List.map_replicate]
      rw [← hlen]
      have he : offset + (decorated offset template rest).length + distance =
          offset + distance + (decorated offset template rest).length := by omega
      rw [he]

theorem decorated_lower {root offset : Nat} {template : Column} (hoff : root ≤ offset)
    (ht : ∀ p ∈ template, root ≤ p) (ranks : List Nat) :
    ParentsAtLeast root (decorated offset template ranks) := by
  induction ranks with
  | nil => simp [decorated, ParentsAtLeast]
  | cons k rest ih =>
      intro c hc p hp
      simp only [decorated, List.mem_append, List.mem_singleton] at hc
      rcases hc with (hc | hc) | hc
      · exact ih c hc p hp
      · subst c; exact ht p hp
      · have he := List.eq_of_mem_replicate hc
        subst c
        simp only [List.mem_singleton] at hp
        omega

structure SproutState where
  front : Matrix
  block : Matrix
  template : Column
  block_nonempty : block ≠ []
  control : template.getLast? = some front.length
  lower : ∀ p ∈ template, front.length ≤ p
  upper : ∀ p ∈ template, p < front.length + block.length

namespace SproutState

def base (s : SproutState) := s.front ++ s.block
def pending (s : SproutState) (ranks : List Nat) := decorated s.base.length s.template ranks
def full (s : SproutState) (ranks : List Nat) := s.base ++ s.pending ranks
def distance (s : SproutState) (ranks : List Nat) := s.block.length + (s.pending ranks).length

theorem pending_lower (s : SproutState) (ranks : List Nat) :
    ParentsAtLeast s.front.length (s.pending ranks) :=
  decorated_lower (by simp [base]) s.lower ranks

theorem full_cons (s : SproutState) (k : Nat) (rest : List Nat) :
    s.full (k :: rest) = sprout (s.full rest) s.template k := by
  simp [full, pending, decorated, sprout, List.length_append, List.append_assoc]

@[simp] theorem full_nil (s : SproutState) : s.full [] = s.base := by simp [full, pending, decorated]

theorem full_nonempty (s : SproutState) (ranks : List Nat) : s.full ranks ≠ [] := by
  intro he
  change (s.front ++ s.block) ++ s.pending ranks = [] at he
  exact s.block_nonempty (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp he).1).2

theorem split_step (s : SproutState) (k : Nat) (rest : List Nat) :
    expand (s.full ((k + 1) :: rest)) 1 = s.full (k :: k :: rest) := by
  rw [s.full_cons, sprout_split, s.full_cons, s.full_cons]

def born (s : SproutState) (ranks : List Nat) : SproutState where
  front := s.full ranks
  block := bornBlock s.front s.block (s.pending ranks) s.template
  template := s.template.map (fun p => p + s.distance ranks)
  block_nonempty := by
    intro he
    have hlen := congrArg List.length he
    rw [bornBlock_length] at hlen
    have hp : 0 < s.block.length := by have := s.block_nonempty; cases s.block <;> simp_all
    simp only [List.length_nil] at hlen
    omega
  control := by
    simp only [List.getLast?_map, s.control, Option.map_some]
    apply congrArg some
    simp only [full, base, distance, List.length_append]
    omega
  lower := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    have := s.lower a ha
    simp only [full, base, distance, List.length_append]
    omega
  upper := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    have := s.upper a ha
    simp only [full, base, distance, List.length_append, bornBlock_length]
    omega

theorem birth_step (s : SproutState) (ranks : List Nat) :
    expand (s.full (0 :: ranks)) 1 = (s.born ranks).full ranks := by
  rw [s.full_cons]
  simp only [sprout, List.replicate_zero, List.append_nil]
  change expand (s.front ++ s.block ++ s.pending ranks ++ [s.template]) 1 = _
  rw [sprout_birth s.front s.block (s.pending ranks) s.template s.block_nonempty (s.pending_lower ranks) s.control]
  have hoff : (s.born ranks).base.length = s.base.length + s.distance ranks := by
    simp only [born, base, full, List.length_append, bornBlock_length, distance]
    omega
  have hp : translated (s.distance ranks) (s.pending ranks) = (s.born ranks).pending ranks := by
    change translated (s.distance ranks) (decorated s.base.length s.template ranks) =
      decorated (s.born ranks).base.length (s.template.map (fun p => p + s.distance ranks)) ranks
    rw [hoff, decorated_translated]
  change s.full ranks ++ bornBlock s.front s.block (s.pending ranks) s.template ++
    translated (s.distance ranks) (s.pending ranks) = _
  rw [hp]
  rfl

end SproutState

def forestSteps : List Nat → Nat
  | [] => 0
  | k :: rest => (2 ^ (k + 1) - 1) + forestSteps rest

def forestBirths : List Nat → Nat
  | [] => 0
  | k :: rest => 2 ^ k + forestBirths rest

theorem forestSteps_split (k : Nat) (rest : List Nat) :
    forestSteps ((k + 1) :: rest) = forestSteps (k :: k :: rest) + 1 := by
  simp only [forestSteps, Nat.pow_succ]
  have := Nat.two_pow_pos k
  omega

theorem forestBirths_split (k : Nat) (rest : List Nat) :
    forestBirths ((k + 1) :: rest) = forestBirths (k :: k :: rest) := by
  simp only [forestBirths, Nat.pow_succ]
  omega

inductive SproutTrace : SproutState → List Nat → SproutState → Nat → Nat → Prop
  | done (s) : SproutTrace s [] s 0 0
  | split {s rest k target steps births} :
      SproutTrace s (k :: k :: rest) target steps births →
      SproutTrace s ((k + 1) :: rest) target (steps + 1) births
  | birth {s rest target steps births} :
      SproutTrace (s.born rest) rest target steps births →
      SproutTrace s (0 :: rest) target (steps + 1) (births + 1)

theorem sprout_run (s : SproutState) (ranks : List Nat) :
    ∃ target, SproutTrace s ranks target (forestSteps ranks) (forestBirths ranks) := by
  generalize he : forestSteps ranks = budget
  induction budget using Nat.strongRecOn generalizing s ranks with
  | ind budget ih =>
      cases ranks with
      | nil => exact ⟨s, by rw [← he]; exact SproutTrace.done s⟩
      | cons k rest =>
          cases k with
          | zero =>
              have hless : forestSteps rest < budget := by simp only [forestSteps] at he; omega
              obtain ⟨target, ht⟩ := ih (forestSteps rest) hless (s.born rest) rest rfl
              refine ⟨target, ?_⟩
              have hh := SproutTrace.birth ht
              simpa only [forestSteps, forestBirths, Nat.pow_zero, Nat.pow_one, Nat.reduceSub,
                Nat.add_comm, ← he] using hh
          | succ k =>
              have hless : forestSteps (k :: k :: rest) < budget := by rw [forestSteps_split] at he; omega
              obtain ⟨target, ht⟩ := ih (forestSteps (k :: k :: rest)) hless s (k :: k :: rest) rfl
              refine ⟨target, ?_⟩
              rw [← he, forestSteps_split, forestBirths_split]
              exact .split ht

theorem SproutTrace.mixedRun {s target : SproutState} {ranks : List Nat} {steps births : Nat}
    (h : SproutTrace s ranks target steps births) :
    PrefixDescent.MixedRun (fun a => expand a 1) (s.full ranks) target.base steps := by
  induction h with
  | done s => simpa only [SproutState.full_nil] using PrefixDescent.MixedRun.refl s.base
  | @split s rest k target steps births _ ih =>
      refine PrefixDescent.MixedRun.step (s.full_nonempty _) ?_ ih
      rw [s.split_step]
      exact ⟨[], by simp⟩
  | @birth s rest target steps births _ ih =>
      refine PrefixDescent.MixedRun.step (s.full_nonempty _) ?_ ih
      rw [s.birth_step]
      exact ⟨[], by simp⟩

#print axioms sprout_run
#print axioms SproutTrace.mixedRun

end LaverLowerBounds.ParentBMS
