# As an example, here is an implementation of
# the first problem "Ryerson Letter Grade":

def ryerson_letter_grade(n):
    if n < 50:
        return 'F'
    elif n > 89:
        return 'A+'
    elif n > 84:
        return 'A'
    elif n > 79:
        return 'A-'
    tens = n // 10
    ones = n % 10
    if ones < 3:
        adjust = "-"
    elif ones > 6:
        adjust = "+"
    else:
        adjust = ""
    return "DCB"[tens - 5] + adjust

def is_ascending(items):
   res=True
   for i in range(1,len(items)):
       if(items[i] <= items[i-1]): # if any item found not greater than previous item
           res=False
           break

   return res

print(is_ascending([])) # returns True
print(is_ascending([-5,10,99,123456])) # returns True
print(is_ascending([2,3,3,4,5])) # returns False
print(is_ascending([-99])) # returns True
print(is_ascending([4,5,6,7,3,7,9])) # returns False
print(is_ascending([1,1,1,1])) # returns False
