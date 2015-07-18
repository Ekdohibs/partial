for i in {15..30}
do
	/usr/bin/time -f "%e," sh -c "echo $i | $1 > /dev/null"
done