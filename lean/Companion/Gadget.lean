import Companion.Kernel

namespace Companion

def SixEquationForcing : Prop :=
  ∀ (G : Type) [Group G] (a b c y1 y2 y3 y4 y5 y6 y7 : G),
    a*a=1 → b*b=1 → c*c=1 → y1*y1=1 → y2*y2=1 →
    y3*y3=1 → y4*y4=1 → y5*y5=1 → y6*y6=1 → y7*y7=1 →
    a*y1*y2=1 → b*y2*y3=1 → y3*y4*y5=1 → a*y5*y6=1 →
    c*y6*y7=1 → y1*y4*y7=1 → y6*y7=y7*y6 → a*b*a=c

private theorem solve_row {G : Type*} [Group G] {a b c : G}
    (ha : a*a=1) (h : a*b*c=1) : a=b*c := by
  apply mul_left_cancel (a := a)
  simpa only [← mul_assoc, ha] using h.symm

private theorem invol_cancel {G : Type*} [Group G] (a y b : G) (hy : y*y=1) :
    (a*y)*(y*b)=a*b := by
  calc
    (a*y)*(y*b) = a*((y*y)*b) := by simp only [mul_assoc]
    _ = a*b := by rw [hy, one_mul]

/-- The exact forcing argument in Appendix B, Step 4. The robust extension
and the rest of the gadget lemma are separate, unfinished obligations. -/
theorem six_equation_forcing : SixEquationForcing := by
  intro G _ a b c y1 y2 y3 y4 y5 y6 y7 ha hb hc h1 h2 h3 h4 h5 h6 h7 e1 e2 e3 e4 e5 e6 comm
  have a12 := solve_row ha e1
  have b23 := solve_row hb e2
  have a56 := solve_row ha e4
  have y345 := solve_row h3 e3
  have y417 : y4=y1*y7 := by
    apply mul_left_cancel (a := y1)
    calc
      y1*y4 = (y1*y4)*(y7*y7) := by rw [h7, mul_one]
      _ = ((y1*y4)*y7)*y7 := by simp only [mul_assoc]
      _ = y7 := by rw [e6, one_mul]
      _ = y1*(y1*y7) := by rw [← mul_assoc, h1, one_mul]
  have c67 := solve_row hc e5
  calc
    a*b*a = (y1*y2)*(y2*y3)*a := by rw [a12, b23]
    _ = (y1*y2)*(y2*y3)*(y5*y6) := by rw [a56]
    _ = (y1*y3)*(y5*y6) := by rw [invol_cancel y1 y2 y3 h2]
    _ = (y1*(y4*y5))*(y5*y6) := by rw [y345]
    _ = (y1*y4)*y6 := by simpa only [← mul_assoc] using invol_cancel (y1*y4) y5 y6 h5
    _ = (y1*(y1*y7))*y6 := by rw [y417]
    _ = y7*y6 := by rw [← mul_assoc y1 y1 y7, h1, one_mul]
    _ = y6*y7 := comm.symm
    _ = c := c67.symm

end Companion
