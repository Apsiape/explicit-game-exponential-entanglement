import Companion.Data
namespace Companion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def target010 : Word := [(11, true), (11, true)]
def certificate010 : List Factor := [⟨.square 10, true, []⟩]
theorem checked010 : check suppliedGame target010 certificate010 42 = true := by decide +kernel
theorem area010 : HasArea suppliedGame target010 42 := check_sound checked010

def target011 : Word := [(12, true), (12, true)]
def certificate011 : List Factor := [⟨.square 11, true, []⟩]
theorem checked011 : check suppliedGame target011 certificate011 42 = true := by decide +kernel
theorem area011 : HasArea suppliedGame target011 42 := check_sound checked011

def target012 : Word := [(13, true), (13, true)]
def certificate012 : List Factor := [⟨.square 12, true, []⟩]
theorem checked012 : check suppliedGame target012 certificate012 42 = true := by decide +kernel
theorem area012 : HasArea suppliedGame target012 42 := check_sound checked012

def target013 : Word := [(14, true), (14, true)]
def certificate013 : List Factor := [⟨.square 13, true, []⟩]
theorem checked013 : check suppliedGame target013 certificate013 42 = true := by decide +kernel
theorem area013 : HasArea suppliedGame target013 42 := check_sound checked013

def target014 : Word := [(15, true), (15, true)]
def certificate014 : List Factor := [⟨.square 14, true, []⟩]
theorem checked014 : check suppliedGame target014 certificate014 42 = true := by decide +kernel
theorem area014 : HasArea suppliedGame target014 42 := check_sound checked014

def target015 : Word := [(16, true), (16, true)]
def certificate015 : List Factor := [⟨.square 15, true, []⟩]
theorem checked015 : check suppliedGame target015 certificate015 42 = true := by decide +kernel
theorem area015 : HasArea suppliedGame target015 42 := check_sound checked015

def target016 : Word := [(17, true), (17, true)]
def certificate016 : List Factor := [⟨.square 16, true, []⟩]
theorem checked016 : check suppliedGame target016 certificate016 42 = true := by decide +kernel
theorem area016 : HasArea suppliedGame target016 42 := check_sound checked016

def target017 : Word := [(18, true), (18, true)]
def certificate017 : List Factor := [⟨.square 17, true, []⟩]
theorem checked017 : check suppliedGame target017 certificate017 42 = true := by decide +kernel
theorem area017 : HasArea suppliedGame target017 42 := check_sound checked017

def target018 : Word := [(19, true), (19, true)]
def certificate018 : List Factor := [⟨.square 18, true, []⟩]
theorem checked018 : check suppliedGame target018 certificate018 42 = true := by decide +kernel
theorem area018 : HasArea suppliedGame target018 42 := check_sound checked018

def target019 : Word := [(20, true), (20, true)]
def certificate019 : List Factor := [⟨.square 19, true, []⟩]
theorem checked019 : check suppliedGame target019 certificate019 42 = true := by decide +kernel
theorem area019 : HasArea suppliedGame target019 42 := check_sound checked019

end Companion
