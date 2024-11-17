rm -rf *backup*
rm -rf *test_ecc*.log*
echo -e "\e[32mRun test: test_ecc_0 \e[0m"
./test_ecc_0.sh -reset_run
./test_ecc_0.sh >> ./test_ecc_0.log
./test_ecc_0.sh -reset_run

echo ""
echo ""
echo -e "\e[32mRun test: test_ecc_1 \e[0m"
./test_ecc_1.sh >> ./test_ecc_1.log
./test_ecc_1.sh -reset_run

echo ""
echo ""
echo -e "\e[32mRun test: test_ecc_2 \e[0m"
./test_ecc_2.sh >> ./test_ecc_2.log
./test_ecc_2.sh -reset_run

echo ""
echo ""
echo -e "\e[32mRun test: test_ecc_3 \e[0m"
./test_ecc_3.sh >> ./test_ecc_3.log
./test_ecc_3.sh -reset_run

rm -rf *backup*
