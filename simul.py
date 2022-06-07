from random import seed
from random import randint
from random import getrandbits
import matplotlib.pyplot as plt
import math
from matplotlib.ticker import PercentFormatter
seed(1)

def calculateReturn(rngNumber, ticketPrice):
  rngBits = [int(x) for x in bin(rngNumber)[2:].zfill(253)[2:]]
  bitSum1 = 0;
  for i in range(0, 128):
      bitSum1 += rngBits[i]
  
  bitSum2 = 0
  for i in range(0, 120):
      bitSum2 += rngBits[i + 100]

  jackPot = 0
  e2 = 1
  for i in range(0, 20):
      jackPot += rngBits[i + 228] * e2
      e2 = e2 + e2

  out = (ticketPrice * (bitSum1 + bitSum2)) // 128

  if jackPot > 2**20 - 10:
      out = out + ticketPrice * 5

  return(out)

ticketPrice = 10000

returns = []
simulations = 10000000
moneyGivenOut = 0
for _ in range (simulations):
    luckyNumber = getrandbits(253)
    output = calculateReturn(luckyNumber, ticketPrice)
    
    returns.append(output/ticketPrice)
    moneyGivenOut = moneyGivenOut + output

print('return%:' + str((simulations*ticketPrice-moneyGivenOut)/(simulations*ticketPrice)*100))     

plt.style.use('ggplot')
plt.hist(returns, bins = 100, histtype='step',
         facecolor='g', linewidth=2.,
         joinstyle='round', density=True)
plt.gca().xaxis.set_major_formatter(PercentFormatter(1))
plt.gca().set_xlabel('Return %')
plt.gca().set_ylabel('Frequency %')
plt.savefig('distribution.png', bbox_inches = 'tight')