arr=[1.225,2.675,1.155,1.9999,21.006,1.9995,6.5,7.5,6.50000001,7.50000001]
for t in arr:
	print "\n-----",t
	print str("%.2f" % (t))
	print round((t),0)
	print round((t),2)
	print int(round((t),0))