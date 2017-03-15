import itertools
import sys

N=None
if len(sys.argv)>1:
	N = int(sys.argv[1])
else:
	print "Please provide the size as first argument"
	sys.exit(0)

ELEMS = range(1,N+1)
id = 0
for n in xrange(1,N+1):
	for toto in  itertools.combinations(ELEMS, n):
		id +=1;
		line = 'let ENUMERATION_'+str(N)+'['+str(id)+'] := {';
		is_first = True
		for i in toto:
			if is_first:
				is_first=False
			else:
				line+=', '
			line += str(i)
				
		line+='};'
		print line