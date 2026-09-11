import GD.Kernel

namespace GD
noncomputable section
open Set

theorem positive_product_interval (a b al au bl bu : ℝ) (hal : 0 ≤ al) (hbl : 0 ≤ bl)
    (ha : a ∈ Icc al au) (hb : b ∈ Icc bl bu) : a*b ∈ Icc (al*bl) (au*bu) :=
  ⟨mul_le_mul ha.1 hb.1 hbl (hal.trans ha.1),mul_le_mul ha.2 hb.2 (hbl.trans hb.1) (hal.trans (ha.1.trans ha.2))⟩

theorem radical_kernel_interval (a b al au bl bu sl su : ℝ)
    (hal : 0 ≤ al) (hbl : 0 ≤ bl) (ha : a ∈ Icc al au) (hb : b ∈ Icc bl bu)
    (hl : sl^2 ≤ al^2+6*al*bl+bl^2) (hu : au^2+6*au*bu+bu^2 ≤ su^2) (hsu : 0 ≤ su) :
    K a b ∈ Icc ((al+bl+sl)/2) ((au+bu+su)/2) := by
  have hlo := K_mono hal hbl ha.1 hb.1
  have hhi := K_mono (hal.trans ha.1) (hbl.trans hb.1) ha.2 hb.2
  have hsl : sl ≤ Real.sqrt (disc al bl) := Real.le_sqrt_of_sq_le hl
  have hsu' : Real.sqrt (disc au bu) ≤ su := Real.sqrt_le_iff.mpr ⟨hsu,hu⟩
  unfold K at hlo hhi
  change (al+bl+sl)/2 ≤ (a+b+Real.sqrt (disc a b))/2 ∧ (a+b+Real.sqrt (disc a b))/2 ≤ (au+bu+su)/2
  exact ⟨by linarith,by linarith⟩

end
end GD
