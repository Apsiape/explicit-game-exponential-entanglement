import Companion.Data
namespace Companion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- C: t1 t2 t1^-1 t2^-1
def derivationTarget10 : Word := [(2, true), (27, true), (2, true), (27, false), (2, false), (27, true), (2, false), (27, false)]
def derivationCertificate10 : List Factor := [⟨.square 1, false, [(2, true), (27, true), (2, true), (27, false)]⟩, ⟨.square 1, false, [(2, true), (27, true), (2, true), (27, false), (2, true), (27, true)]⟩, ⟨.pConjugacy 7, true, [(2, true)]⟩, ⟨.pConjugacy 7, true, [(2, true), (13, true), (2, true)]⟩, ⟨.conjugacy 61, true, []⟩, ⟨.square 12, true, []⟩]
theorem derivationCheck10 : checkWith (presentationRelator inputPresentation) derivationTarget10 derivationCertificate10 60 = true := by decide +kernel
theorem derivationArea10 : HasAreaWith (presentationRelator inputPresentation) derivationTarget10 60 := checkWith_sound derivationCheck10

-- A: d t1 D t2^-1 t1^-1
def derivationTarget11 : Word := [(3, true), (2, true), (3, false), (27, true), (2, false), (27, false), (2, false)]
def derivationCertificate11 : List Factor := [⟨.square 2, false, [(3, true), (2, true)]⟩, ⟨.square 1, false, [(3, true), (2, true), (3, true), (27, true)]⟩, ⟨.square 1, false, [(3, true), (2, true), (3, true), (27, true), (2, true), (27, false)]⟩, ⟨.pConjugacy 7, true, [(3, true), (2, true), (3, true)]⟩, ⟨.conjugacy 1, true, []⟩, ⟨.conjugacy 46, true, [(13, false)]⟩, ⟨.square 12, false, []⟩, ⟨.equation 1, true, [(2, false)]⟩]
theorem derivationCheck11 : checkWith (presentationRelator inputPresentation) derivationTarget11 derivationCertificate11 60 = true := by decide +kernel
theorem derivationArea11 : HasAreaWith (presentationRelator inputPresentation) derivationTarget11 60 := checkWith_sound derivationCheck11

-- A: d t2 D t2^-1
def derivationTarget12 : Word := [(3, true), (27, true), (2, true), (27, false), (3, false), (27, true), (2, false), (27, false)]
def derivationCertificate12 : List Factor := [⟨.square 2, false, [(3, true), (27, true), (2, true), (27, false)]⟩, ⟨.square 1, false, [(3, true), (27, true), (2, true), (27, false), (3, true), (27, true)]⟩, ⟨.pConjugacy 7, true, [(3, true)]⟩, ⟨.pConjugacy 7, true, [(3, true), (13, true), (3, true)]⟩, ⟨.conjugacy 45, true, [(3, true)]⟩, ⟨.square 2, true, []⟩]
theorem derivationCheck12 : checkWith (presentationRelator inputPresentation) derivationTarget12 derivationCertificate12 60 = true := by decide +kernel
theorem derivationArea12 : HasAreaWith (presentationRelator inputPresentation) derivationTarget12 60 := checkWith_sound derivationCheck12

-- A: d t3 D t3^-1
def derivationTarget13 : Word := [(3, true), (27, true), (27, true), (2, true), (27, false), (27, false), (3, false), (27, true), (27, true), (2, false), (27, false), (27, false)]
def derivationCertificate13 : List Factor := [⟨.square 2, false, [(3, true), (27, true), (27, true), (2, true), (27, false), (27, false)]⟩, ⟨.square 1, false, [(3, true), (27, true), (27, true), (2, true), (27, false), (27, false), (3, true), (27, true), (27, true)]⟩, ⟨.pConjugacy 7, true, [(3, true), (27, true)]⟩, ⟨.pConjugacy 4, true, [(3, true)]⟩, ⟨.pConjugacy 7, true, [(3, true), (17, true), (3, true), (27, true)]⟩, ⟨.pConjugacy 4, true, [(3, true), (17, true), (3, true)]⟩, ⟨.conjugacy 11, true, [(3, true)]⟩, ⟨.square 2, true, []⟩]
theorem derivationCheck13 : checkWith (presentationRelator inputPresentation) derivationTarget13 derivationCertificate13 60 = true := by decide +kernel
theorem derivationArea13 : HasAreaWith (presentationRelator inputPresentation) derivationTarget13 60 := checkWith_sound derivationCheck13

-- Z: p x P X
def derivationTarget14 : Word := [(27, true), (4, true), (27, false), (4, false)]
def derivationCertificate14 : List Factor := [⟨.square 3, false, [(27, true), (4, true), (27, false)]⟩, ⟨.pConjugacy 8, true, []⟩, ⟨.square 3, true, []⟩]
theorem derivationCheck14 : checkWith (presentationRelator inputPresentation) derivationTarget14 derivationCertificate14 60 = true := by decide +kernel
theorem derivationArea14 : HasAreaWith (presentationRelator inputPresentation) derivationTarget14 60 := checkWith_sound derivationCheck14

-- Z: p z P Z
def derivationTarget15 : Word := [(27, true), (5, true), (27, false), (5, false)]
def derivationCertificate15 : List Factor := [⟨.square 4, false, [(27, true), (5, true), (27, false)]⟩, ⟨.pConjugacy 9, true, []⟩, ⟨.square 4, true, []⟩]
theorem derivationCheck15 : checkWith (presentationRelator inputPresentation) derivationTarget15 derivationCertificate15 60 = true := by decide +kernel
theorem derivationArea15 : HasAreaWith (presentationRelator inputPresentation) derivationTarget15 60 := checkWith_sound derivationCheck15

-- Z: q x Q X
def derivationTarget16 : Word := [(1, true), (27, true), (1, true), (4, true), (1, false), (27, false), (1, false), (4, false)]
def derivationCertificate16 : List Factor := [⟨.square 0, false, [(1, true), (27, true), (1, true), (4, true)]⟩, ⟨.square 0, false, [(1, true), (27, true), (1, true), (4, true), (1, true), (27, false)]⟩, ⟨.square 3, false, [(1, true), (27, true), (1, true), (4, true), (1, true), (27, false), (1, true)]⟩, ⟨.pConjugacy 5, true, [(1, true)]⟩, ⟨.pConjugacy 8, true, [(1, true), (7, true)]⟩, ⟨.pConjugacy 5, true, [(1, true), (7, true), (4, true)]⟩, ⟨.conjugacy 7, true, [(1, true)]⟩, ⟨.conjugacy 67, true, [(1, true)]⟩, ⟨.square 0, true, []⟩]
theorem derivationCheck16 : checkWith (presentationRelator inputPresentation) derivationTarget16 derivationCertificate16 60 = true := by decide +kernel
theorem derivationArea16 : HasAreaWith (presentationRelator inputPresentation) derivationTarget16 60 := checkWith_sound derivationCheck16

-- Z: q z Q Z
def derivationTarget17 : Word := [(1, true), (27, true), (1, true), (5, true), (1, false), (27, false), (1, false), (5, false)]
def derivationCertificate17 : List Factor := [⟨.square 0, false, [(1, true), (27, true), (1, true), (5, true)]⟩, ⟨.square 0, false, [(1, true), (27, true), (1, true), (5, true), (1, true), (27, false)]⟩, ⟨.square 4, false, [(1, true), (27, true), (1, true), (5, true), (1, true), (27, false), (1, true)]⟩, ⟨.pConjugacy 5, true, [(1, true)]⟩, ⟨.pConjugacy 9, true, [(1, true), (7, true)]⟩, ⟨.pConjugacy 5, true, [(1, true), (7, true), (5, true)]⟩, ⟨.conjugacy 8, true, [(1, true)]⟩, ⟨.conjugacy 73, true, [(1, true)]⟩, ⟨.square 0, true, []⟩]
theorem derivationCheck17 : checkWith (presentationRelator inputPresentation) derivationTarget17 derivationCertificate17 60 = true := by decide +kernel
theorem derivationArea17 : HasAreaWith (presentationRelator inputPresentation) derivationTarget17 60 := checkWith_sound derivationCheck17

-- Z: d x D X
def derivationTarget18 : Word := [(3, true), (4, true), (3, false), (4, false)]
def derivationCertificate18 : List Factor := [⟨.square 2, false, [(3, true), (4, true)]⟩, ⟨.square 3, false, [(3, true), (4, true), (3, true)]⟩, ⟨.conjugacy 64, true, [(3, true)]⟩, ⟨.square 2, true, []⟩]
theorem derivationCheck18 : checkWith (presentationRelator inputPresentation) derivationTarget18 derivationCertificate18 60 = true := by decide +kernel
theorem derivationArea18 : HasAreaWith (presentationRelator inputPresentation) derivationTarget18 60 := checkWith_sound derivationCheck18

-- Z: d z D Z
def derivationTarget19 : Word := [(3, true), (5, true), (3, false), (5, false)]
def derivationCertificate19 : List Factor := [⟨.square 2, false, [(3, true), (5, true)]⟩, ⟨.square 4, false, [(3, true), (5, true), (3, true)]⟩, ⟨.conjugacy 70, true, [(3, true)]⟩, ⟨.square 2, true, []⟩]
theorem derivationCheck19 : checkWith (presentationRelator inputPresentation) derivationTarget19 derivationCertificate19 60 = true := by decide +kernel
theorem derivationArea19 : HasAreaWith (presentationRelator inputPresentation) derivationTarget19 60 := checkWith_sound derivationCheck19

end Companion
