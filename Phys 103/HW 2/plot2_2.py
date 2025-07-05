import matplotlib.pyplot as plt
import numpy as np
import math

#define set of constants (Note: all need to be positive)
#fixed constant
w_0 = 2 
f_0 = 4
m=1
#array of constants
Tw_0 = [math.pi,4] #the first is never in phase, while the second always in phase with some term
Q = [1,20] #provide two different quality factors

#define the sum of solutions approximation, with n=10
def x(Tw, q, t): #here, Tw represents the Tw_0 chosen
   output = 0

   for n in range(1,31):
      w = 2* math.pi * n/(Tw)*w_0 #the frequency
      B = 1-(2 * math.pi * n/(Tw))**2 #coefficient of sin term
      C = 2* math.pi * n/(q * Tw) #coefficient of cos term

      A = (-1)**(n+1) * f_0 / (n * math.pi) * 1/(m * w_0**2 * (B**2+C**2)) #amplitude
      output += A*(B*math.sin(w*t)-C*math.cos(w*t))

   return output

#plot functions
for i in range(2): #for Tw_0
   for j in range(2): #for Q
        t = np.arange(-10, 10, 0.01)

        Tw = Tw_0[i]
        q = Q[j]

        #add X list
        X = []
        for k in range(len(t)):
            X.append(x(Tw, q, t[k]))

        #plot function on graph
        plt.plot(t,X, lw=2)
        plt.ylim(-0.25,0.25)

        plt.savefig(str(i)+','+str(j)+'.png') #save graph
        plt.clf() #clear graph