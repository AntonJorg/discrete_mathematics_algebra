
class Group (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

attribute [simp] Group.mul_assoc Group.one_mul Group.mul_left_inv


namespace Group

variable {G : Type} [Group G]

-- We can 'divide out' from the left
@[simp]
theorem mul_left_cancel (a b c : G) (h: a * b = a * c) : b = c := by
   rw [← one_mul c]
   rw [← mul_left_inv a]
   rw [mul_assoc]
   rw [← h]
   rw [← mul_assoc]
   rw [mul_left_inv]
   rw [one_mul]

-- Proof by calc instead (not working!!)
--theorem mul_left_cancel' (a b c : G) (hyp: a * b = a * c) : b = c :=
--calc b
-- _ = 1 * c := by rw [← id_mul c]
--  _ = a⁻¹ * a * b := by rw [← mul_left_inv]
--  _ = a⁻¹ * (a * b) := by rw [mul_assoc]
--  _ = a⁻¹ * (a * c) := by rw [← hyp]
--  _ = a⁻¹ * a * c := by rw [← mul_assoc]
--  _ = 1 * c := by rw [mul_left_inv]
--  _ = c := by rw [id_mul]

@[simp]
theorem mul_eq_of_eq_inv_mul (a x y : G) (h : x = a⁻¹ * y) : a * x = y := by
  apply mul_left_cancel a⁻¹
  rw [← h]
  rw [← mul_assoc]
  rw [mul_left_inv]
  rw [one_mul]

-- The identity is also a right identity (only left is an axiom)
@[simp]
theorem mul_one (a : G) : a * 1 = a := by
  apply mul_eq_of_eq_inv_mul
  rw [mul_left_inv]

-- All elements have right inverses (only left is an axiom)
@[simp]
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  apply mul_eq_of_eq_inv_mul
  rw [mul_one]

-- We can 'divide out' from the right
@[simp]
theorem mul_right_cancel (a b c : G) (hyp: b * a = c * a) : b = c := by
   rw [← mul_one c]
   rw [← mul_right_inv a]
   rw [← mul_assoc]
   rw [← hyp]
   rw [mul_assoc]
   rw [mul_right_inv]
   rw [mul_one]

-- Lemma 3.1.7, Uniqueness of identity
theorem identity_is_unique (e1 e2 f : G) (h1 : e1 * f = f) (h2 : e2 * f = f) : e1 = e2 := by
  apply mul_right_cancel f
  rw [h1]
  rw [h2]


theorem eq_mul_inv_of_mul_eq (a b c : G) (h : a * c = b) : a = b * c⁻¹ := by
  rw [← h]
  rw [mul_assoc]
  rw [mul_right_inv]
  rw [mul_one]

theorem eq_inv_of_mul_eq_one (a b : G) (h : a * b = 1) : a = b⁻¹ := by
  apply mul_right_cancel b
  rw [h, mul_left_inv]

-- The inverse of the inverse of a is a itself
@[simp]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a := by
  symm
  apply eq_inv_of_mul_eq_one
  rw [mul_right_inv]

-- If multiplication with a from the left has no effect, a = 1
@[simp]
theorem mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 := by
  constructor -- Split bi-implication
  -- Right implication
  {
    intro h
    rw [← mul_right_cancel b a 1]
    rw [one_mul]
    exact h
  }
  -- Left implication
  {
    intro h
    rw [h]
    rw [one_mul]
  }

-- If multiplication with b from the right has no effect, b = 1
@[simp]
theorem mul_right_eq_self (a b : G) : a * b = a ↔ b = 1 := by
  constructor -- Split bi-implication
  -- Right implication
  {
    intro h
    rw [← mul_left_cancel a b 1]
    rw [mul_one]
    exact h
  }
  -- Left implication
  {
    intro h
    rw [h]
    rw [mul_one]
  }

-- The identity is its own inverse
theorem one_inv : (1 : G)⁻¹ = 1 := by
  rw [← one_mul 1⁻¹]
  symm
  apply eq_mul_inv_of_mul_eq
  rw [mul_one]

@[simp]
theorem inv_inj_iff (a b : G): a⁻¹ = b⁻¹ ↔ a = b := by
  constructor
  {
    intro h
    rw [← inv_inv a, h, inv_inv b]
  }
  {
    intro h
    rw [h]
  }

-- If a is the inverse of b, then b is the inverse of a
theorem inv_eq {a b : G}: a⁻¹ = b ↔ b⁻¹ = a := by
  constructor
  {
    intro h
    rw [← h]
    rw [inv_inv]
  }
  {
    intro h
    rw [← h]
    rw [inv_inv]
  }

end Group
