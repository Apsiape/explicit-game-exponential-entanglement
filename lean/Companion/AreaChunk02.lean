import Companion.Data
namespace Companion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def target020 : Word := [(21, true), (21, true)]
def certificate020 : List Factor := [⟨.square 20, true, []⟩]
theorem checked020 : check suppliedGame target020 certificate020 42 = true := by decide +kernel
theorem area020 : HasArea suppliedGame target020 42 := check_sound checked020

def target021 : Word := [(22, true), (22, true)]
def certificate021 : List Factor := [⟨.square 21, true, []⟩]
theorem checked021 : check suppliedGame target021 certificate021 42 = true := by decide +kernel
theorem area021 : HasArea suppliedGame target021 42 := check_sound checked021

def target022 : Word := [(23, true), (23, true)]
def certificate022 : List Factor := [⟨.square 22, true, []⟩]
theorem checked022 : check suppliedGame target022 certificate022 42 = true := by decide +kernel
theorem area022 : HasArea suppliedGame target022 42 := check_sound checked022

def target023 : Word := [(24, true), (24, true)]
def certificate023 : List Factor := [⟨.square 23, true, []⟩]
theorem checked023 : check suppliedGame target023 certificate023 42 = true := by decide +kernel
theorem area023 : HasArea suppliedGame target023 42 := check_sound checked023

def target024 : Word := [(25, true), (25, true)]
def certificate024 : List Factor := [⟨.square 24, true, []⟩]
theorem checked024 : check suppliedGame target024 certificate024 42 = true := by decide +kernel
theorem area024 : HasArea suppliedGame target024 42 := check_sound checked024

def target025 : Word := [(26, true), (26, true)]
def certificate025 : List Factor := [⟨.square 25, true, []⟩]
theorem checked025 : check suppliedGame target025 certificate025 42 = true := by decide +kernel
theorem area025 : HasArea suppliedGame target025 42 := check_sound checked025

def target026 : Word := [(1, true), (6, true), (9, true)]
def certificate026 : List Factor := [⟨.equation 0, true, []⟩]
theorem checked026 : check suppliedGame target026 certificate026 42 = true := by decide +kernel
theorem area026 : HasArea suppliedGame target026 42 := check_sound checked026

def target027 : Word := [(2, true), (13, true), (16, true)]
def certificate027 : List Factor := [⟨.equation 1, true, []⟩]
theorem checked027 : check suppliedGame target027 certificate027 42 = true := by decide +kernel
theorem area027 : HasArea suppliedGame target027 42 := check_sound checked027

def target028 : Word := [(2, true), (21, true), (23, true)]
def certificate028 : List Factor := [⟨.equation 2, true, []⟩]
theorem checked028 : check suppliedGame target028 certificate028 42 = true := by decide +kernel
theorem area028 : HasArea suppliedGame target028 42 := check_sound checked028

def target029 : Word := [(2, true), (25, true), (26, true)]
def certificate029 : List Factor := [⟨.equation 3, true, []⟩]
theorem checked029 : check suppliedGame target029 certificate029 42 = true := by decide +kernel
theorem area029 : HasArea suppliedGame target029 42 := check_sound checked029

end Companion
