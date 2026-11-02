import Companion.Data
namespace Companion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- L: x x
def derivationTarget20 : Word := [(4, true), (4, true)]
def derivationCertificate20 : List Factor := [⟨.square 3, true, []⟩]
theorem derivationCheck20 : checkWith (presentationRelator inputPresentation) derivationTarget20 derivationCertificate20 60 = true := by decide +kernel
theorem derivationArea20 : HasAreaWith (presentationRelator inputPresentation) derivationTarget20 60 := checkWith_sound derivationCheck20

-- L: z z
def derivationTarget21 : Word := [(5, true), (5, true)]
def derivationCertificate21 : List Factor := [⟨.square 4, true, []⟩]
theorem derivationCheck21 : checkWith (presentationRelator inputPresentation) derivationTarget21 derivationCertificate21 60 = true := by decide +kernel
theorem derivationArea21 : HasAreaWith (presentationRelator inputPresentation) derivationTarget21 60 := checkWith_sound derivationCheck21

-- L: x z x z x z x z
def derivationTarget22 : Word := [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true), (4, true), (5, true)]
def derivationCertificate22 : List Factor := [⟨.conjugacy 75, true, [(4, true)]⟩, ⟨.conjugacy 75, true, [(4, true), (19, true), (4, true)]⟩, ⟨.conjugacy 17, true, [(4, true)]⟩, ⟨.square 3, true, []⟩]
theorem derivationCheck22 : checkWith (presentationRelator inputPresentation) derivationTarget22 derivationCertificate22 60 = true := by decide +kernel
theorem derivationArea22 : HasAreaWith (presentationRelator inputPresentation) derivationTarget22 60 := checkWith_sound derivationCheck22

-- P: x t x T X t X T
def derivationTarget23 : Word := [(4, true), (2, true), (4, true), (2, false), (4, false), (2, true), (4, false), (2, false)]
def derivationCertificate23 : List Factor := [⟨.square 1, false, [(4, true), (2, true), (4, true)]⟩, ⟨.square 3, false, [(4, true), (2, true), (4, true), (2, true)]⟩, ⟨.square 3, false, [(4, true), (2, true), (4, true), (2, true), (4, true), (2, true)]⟩, ⟨.square 1, false, [(4, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true)]⟩, ⟨.conjugacy 68, true, []⟩, ⟨.conjugacy 68, true, [(21, true), (2, true)]⟩, ⟨.conjugacy 20, true, []⟩, ⟨.square 1, true, []⟩]
theorem derivationCheck23 : checkWith (presentationRelator inputPresentation) derivationTarget23 derivationCertificate23 60 = true := by decide +kernel
theorem derivationArea23 : HasAreaWith (presentationRelator inputPresentation) derivationTarget23 60 := checkWith_sound derivationCheck23

-- P: x t z T X t Z T
def derivationTarget24 : Word := [(4, true), (2, true), (5, true), (2, false), (4, false), (2, true), (5, false), (2, false)]
def derivationCertificate24 : List Factor := [⟨.square 1, false, [(4, true), (2, true), (5, true)]⟩, ⟨.square 3, false, [(4, true), (2, true), (5, true), (2, true)]⟩, ⟨.square 4, false, [(4, true), (2, true), (5, true), (2, true), (4, true), (2, true)]⟩, ⟨.square 1, false, [(4, true), (2, true), (5, true), (2, true), (4, true), (2, true), (5, true)]⟩, ⟨.conjugacy 63, true, [(4, true)]⟩, ⟨.conjugacy 66, true, []⟩, ⟨.conjugacy 63, true, [(24, true)]⟩, ⟨.square 23, true, []⟩]
theorem derivationCheck24 : checkWith (presentationRelator inputPresentation) derivationTarget24 derivationCertificate24 60 = true := by decide +kernel
theorem derivationArea24 : HasAreaWith (presentationRelator inputPresentation) derivationTarget24 60 := checkWith_sound derivationCheck24

-- P: z t x T Z t X T
def derivationTarget25 : Word := [(5, true), (2, true), (4, true), (2, false), (5, false), (2, true), (4, false), (2, false)]
def derivationCertificate25 : List Factor := [⟨.square 1, false, [(5, true), (2, true), (4, true)]⟩, ⟨.square 4, false, [(5, true), (2, true), (4, true), (2, true)]⟩, ⟨.square 3, false, [(5, true), (2, true), (4, true), (2, true), (5, true), (2, true)]⟩, ⟨.square 1, false, [(5, true), (2, true), (4, true), (2, true), (5, true), (2, true), (4, true)]⟩, ⟨.conjugacy 62, true, [(5, true)]⟩, ⟨.conjugacy 72, true, []⟩, ⟨.conjugacy 62, true, [(22, true)]⟩, ⟨.square 21, true, []⟩]
theorem derivationCheck25 : checkWith (presentationRelator inputPresentation) derivationTarget25 derivationCertificate25 60 = true := by decide +kernel
theorem derivationArea25 : HasAreaWith (presentationRelator inputPresentation) derivationTarget25 60 := checkWith_sound derivationCheck25

-- P: z t z T Z t Z T
def derivationTarget26 : Word := [(5, true), (2, true), (5, true), (2, false), (5, false), (2, true), (5, false), (2, false)]
def derivationCertificate26 : List Factor := [⟨.square 1, false, [(5, true), (2, true), (5, true)]⟩, ⟨.square 4, false, [(5, true), (2, true), (5, true), (2, true)]⟩, ⟨.square 4, false, [(5, true), (2, true), (5, true), (2, true), (5, true), (2, true)]⟩, ⟨.square 1, false, [(5, true), (2, true), (5, true), (2, true), (5, true), (2, true), (5, true)]⟩, ⟨.conjugacy 74, true, []⟩, ⟨.conjugacy 74, true, [(25, true), (2, true)]⟩, ⟨.conjugacy 32, true, []⟩, ⟨.square 1, true, []⟩]
theorem derivationCheck26 : checkWith (presentationRelator inputPresentation) derivationTarget26 derivationCertificate26 60 = true := by decide +kernel
theorem derivationArea26 : HasAreaWith (presentationRelator inputPresentation) derivationTarget26 60 := checkWith_sound derivationCheck26

-- K: J t J^-1 T
def derivationTarget27 : Word := [(4, true), (5, true), (4, true), (5, true), (2, true), (5, false), (4, false), (5, false), (4, false), (2, false)]
def derivationCertificate27 : List Factor := [⟨.square 4, false, [(4, true), (5, true), (4, true), (5, true), (2, true)]⟩, ⟨.square 3, false, [(4, true), (5, true), (4, true), (5, true), (2, true), (5, true)]⟩, ⟨.square 4, false, [(4, true), (5, true), (4, true), (5, true), (2, true), (5, true), (4, true)]⟩, ⟨.square 3, false, [(4, true), (5, true), (4, true), (5, true), (2, true), (5, true), (4, true), (5, true)]⟩, ⟨.square 1, false, [(4, true), (5, true), (4, true), (5, true), (2, true), (5, true), (4, true), (5, true), (4, true)]⟩, ⟨.conjugacy 69, true, []⟩, ⟨.conjugacy 74, true, [(18, true)]⟩, ⟨.conjugacy 69, true, [(18, true), (25, true)]⟩, ⟨.conjugacy 14, true, []⟩, ⟨.square 1, true, []⟩]
theorem derivationCheck27 : checkWith (presentationRelator inputPresentation) derivationTarget27 derivationCertificate27 60 = true := by decide +kernel
theorem derivationArea27 : HasAreaWith (presentationRelator inputPresentation) derivationTarget27 60 := checkWith_sound derivationCheck27

-- Jlink: (xz)^2 w^-1
def derivationTarget28 : Word := [(4, true), (5, true), (4, true), (5, true), (20, false)]
def derivationCertificate28 : List Factor := [⟨.square 19, false, [(4, true), (5, true), (4, true), (5, true)]⟩, ⟨.conjugacy 75, true, [(4, true)]⟩, ⟨.equation 4, true, []⟩]
theorem derivationCheck28 : checkWith (presentationRelator inputPresentation) derivationTarget28 derivationCertificate28 60 = true := by decide +kernel
theorem derivationArea28 : HasAreaWith (presentationRelator inputPresentation) derivationTarget28 60 := checkWith_sound derivationCheck28

end Companion
