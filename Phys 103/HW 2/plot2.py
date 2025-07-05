import matplotlib.pyplot as plt
import numpy as np
import math

#define constant (Note: both need to be positive)
T = 4
f_0 = 4

#define original function
def f(t):
   return f_0*(t/T - math.floor(1/2+t/T))

#define fourier series approximation, with n=10
def fourier(t):
   output = 0

   for n in range(1,11):
      output += (-1)**(n+1) * f_0 / (n* math.pi) * math.sin(2*n* math.pi * t/T)

   return output

#plot function
t = np.arange(-f_0, f_0, 0.01)

Function = []
Fourier = []
for i in range(len(t)):
   Function.append(f(t[i]))
   Fourier.append(fourier(t[i]))

plt.plot(t,Function, lw=2, label='Function f(t)')
plt.plot(t,Fourier, lw=2, label = 'Fourier Approximation')
plt.ylim(-T,T)

plt.legend()
plt.show()