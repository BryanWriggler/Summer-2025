import matplotlib.pyplot as plt
import numpy as np
import math

#define constant
c = 2
P = 2
t_0 = 1/(2*c*math.sqrt(P))-1/(2*math.sqrt(c*math.sqrt(P)))+1/8 #switching time
C = (math.sqrt(2*t_0)-1/math.sqrt(c*math.sqrt(P)))*math.exp((c*math.sqrt(P)+2*math.sqrt(c*math.sqrt(P)))*t_0) #constant for exponential function

#define velocity
def v(t):
 if(t <= t_0): return math.sqrt(2*t) #ignore air resistance
 else: return C*math.exp(-(c*math.sqrt(P)+2*math.sqrt(c*math.sqrt(P)))*t)+1/math.sqrt(c*math.sqrt(P)) #include air resistance, approximated

#plot velocity
t = np.arange(0, 0.8, 0.02)

velocity = []
for i in range(len(t)):
   velocity.append(v(t[i]))

plt.plot(t,velocity, lw=2)
plt.ylim(-0.05,0.65)

plt.show()