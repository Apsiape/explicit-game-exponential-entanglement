import Companion.Data
namespace Companion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def target000 : Word := [(1, true), (1, true)]
def certificate000 : List Factor := [⟨.square 0, true, []⟩]
theorem checked000 : check suppliedGame target000 certificate000 42 = true := by decide +kernel
theorem area000 : HasArea suppliedGame target000 42 := check_sound checked000

def target001 : Word := [(2, true), (2, true)]
def certificate001 : List Factor := [⟨.square 1, true, []⟩]
theorem checked001 : check suppliedGame target001 certificate001 42 = true := by decide +kernel
theorem area001 : HasArea suppliedGame target001 42 := check_sound checked001

def target002 : Word := [(3, true), (3, true)]
def certificate002 : List Factor := [⟨.square 2, true, []⟩]
theorem checked002 : check suppliedGame target002 certificate002 42 = true := by decide +kernel
theorem area002 : HasArea suppliedGame target002 42 := check_sound checked002

def target003 : Word := [(4, true), (4, true)]
def certificate003 : List Factor := [⟨.square 3, true, []⟩]
theorem checked003 : check suppliedGame target003 certificate003 42 = true := by decide +kernel
theorem area003 : HasArea suppliedGame target003 42 := check_sound checked003

def target004 : Word := [(5, true), (5, true)]
def certificate004 : List Factor := [⟨.square 4, true, []⟩]
theorem checked004 : check suppliedGame target004 certificate004 42 = true := by decide +kernel
theorem area004 : HasArea suppliedGame target004 42 := check_sound checked004

def target005 : Word := [(6, true), (6, true)]
def certificate005 : List Factor := [⟨.square 5, true, []⟩]
theorem checked005 : check suppliedGame target005 certificate005 42 = true := by decide +kernel
theorem area005 : HasArea suppliedGame target005 42 := check_sound checked005

def target006 : Word := [(7, true), (7, true)]
def certificate006 : List Factor := [⟨.square 6, true, []⟩]
theorem checked006 : check suppliedGame target006 certificate006 42 = true := by decide +kernel
theorem area006 : HasArea suppliedGame target006 42 := check_sound checked006

def target007 : Word := [(8, true), (8, true)]
def certificate007 : List Factor := [⟨.square 7, true, []⟩]
theorem checked007 : check suppliedGame target007 certificate007 42 = true := by decide +kernel
theorem area007 : HasArea suppliedGame target007 42 := check_sound checked007

def target008 : Word := [(9, true), (9, true)]
def certificate008 : List Factor := [⟨.square 8, true, []⟩]
theorem checked008 : check suppliedGame target008 certificate008 42 = true := by decide +kernel
theorem area008 : HasArea suppliedGame target008 42 := check_sound checked008

def target009 : Word := [(10, true), (10, true)]
def certificate009 : List Factor := [⟨.square 9, true, []⟩]
theorem checked009 : check suppliedGame target009 certificate009 42 = true := by decide +kernel
theorem area009 : HasArea suppliedGame target009 42 := check_sound checked009

end Companion
