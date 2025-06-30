import matplotlib.pyplot as plt
import numpy as np
import math

#define constant
c = 2
P = 8
t_0 = 1/8
v_t = (P/c)**(1/3)

D = (c*(v_t**3) - P)/(2*c*(v_t**3)+P) #coefficient appears in constant term
E = 2*c*(v_t**3)/P #coefficient appears in the exponent

#define velocity
def v(t):
 if(t <= t_0): return math.sqrt(2*t) #ignore air resistance
 else: return 1-D+(D-1/2)*math.exp(-E*(t-1/8)) #include air resistance

#plot velocity
t = np.arange(0, 1.5, 0.02)

velocity = []
for i in range(len(t)):
   velocity.append(v(t[i]))

plt.plot(t,velocity, lw=2)
plt.ylim(-0.05,1.1)

plt.show()