function test_prog
	for i in (seq $argv[1]); $argv[2] > ./lines.txt; end
	if test (uniq < ./lines.txt | wc -l) -eq 1
    		echo "Results are consistent"
	else
    		echo "!!!!! Results are not consistent"
	end
end
