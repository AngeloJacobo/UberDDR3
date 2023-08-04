![mpr_4](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/519c6cd1-3f11-4790-a6bc-7fd7b63f66d1)
![mpr_3](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/2f3bd9bf-4e7b-4cac-8528-34156c89fc2e)
![mpr_2](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/8a631e87-fb64-4de6-8b97-6d4e11eabcce)
![first_mpr](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/f0367289-5575-4fce-b70d-0e00e520be73)
![cntvalue_increments_until_end](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/0a90ac6b-07f2-4d9e-a95e-d9eb60523d81)
# DDR3_Controller
# :construction: :construction_worker_man: :construction_worker_man:  UNDER CONSTRUCTION :construction_worker_man: :construction_worker_man: :construction: 

## Sequential Read
![image](https://user-images.githubusercontent.com/87559347/230342721-c5a575db-0518-4771-a5e6-7fa7e3044273.png)  

## Sequential Read then Sequential Write
![image](https://user-images.githubusercontent.com/87559347/230336798-619a629d-9f7d-431f-8887-a05965b1c70a.png)


## Random Access
![image](https://user-images.githubusercontent.com/87559347/230362722-256dafff-04c1-4052-b664-6b3d234d9089.png)

## Sequential Read Until Next Bank
![image](https://user-images.githubusercontent.com/87559347/230366265-a10b22b1-8113-46f7-9980-f8938a0b4a0c.png)

# PHY Interface    
## WRITE OPERATION   

![image](https://user-images.githubusercontent.com/87559347/233351111-10434e18-4c5c-4751-95c5-536288c514ed.png)

## Sequential Write


![image](https://user-images.githubusercontent.com/87559347/233395320-66a16ad8-1d56-4850-b82e-39abda92366f.png)

## BITSLIP_DQS_TRAIN STATE:

![image](https://user-images.githubusercontent.com/87559347/234852977-21656591-5a52-4916-8546-caa929f273cc.png)

## MPR_READ STATE:
![image](https://user-images.githubusercontent.com/87559347/234854161-3d8ed26a-3ddf-4cf6-a440-616361ee5715.png)

## BITSLIP_DQ_TRAIN STATE: 
![image](https://user-images.githubusercontent.com/87559347/234854620-39d95493-ecc8-4b8f-b391-0f532fff5760.png)


## Sequential Read:
![image](https://user-images.githubusercontent.com/87559347/234856001-ab9056fe-cee1-47b6-a7b7-347ee5138c4f.png)

## PER LANE READ CALIBRATION 
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/827c9097-dc13-47ad-b8c3-3a505108a327)


## AFTER READ CALIBRATION
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/02128baa-19d0-4268-9cfd-93ab70ae2288)

## LANES NOT IN SYNC
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/a4ccc6fb-3a07-4f09-adc5-b7d45b430323)

## SAMPLE READ 1 
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/37147480-339b-41fb-8e00-77218c4c7ad1)

## SAMPLE READ 2 (UNIFORM DELAY DIFFERENCE, 0 slow_clk ABSOLUTE DELAY)
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/7b27e335-0854-49fe-bd68-9b18aae21abd)

## SAMPLE READ 3 (UNIFORM DELAY DIFFERENCE, 2 slow_clk ABSOLUTE DELAY)
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/330aa43e-baaa-4201-bc46-990662c18156)

## SAMPLE READ 4 (RANDOM DELAY DIFFERENCE, 0 slow_clk ABSOLUTE DELAY)
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/cfe39227-d5ea-4ccd-b943-3ee07dbb9b23)

## SAMPLE READ 5 (RANDOM DELAY DIFFERENCE, 2 slow_clk ABSOLUTE DELAY)
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/cf50d5d1-91bb-4581-9d5e-bd4f05aee53d)


## Autofpga "make autofpga"
![Screenshot from 2023-05-18 11-49-19](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/0144ca4c-616e-420c-b464-6e71bf540041)


## Implementation!!
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/763eea4b-a330-4f45-8d0a-672c5643b5dc)

![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/ef9af6cc-3a9a-47ec-a45c-f21d30edc9d5)

## Successful Synthesis-to-Bitstream Generation
![Screenshot from 2023-05-25 19-38-39](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/eb89a6a3-2aab-4c1b-8fbc-f9ecfe508ebd)
![Screenshot from 2023-05-25 19-38-50](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/d6bf96db-6aa5-48b0-a9e4-2288306c0ef7)

## Model Test  

![Screenshot from 2023-06-01 18-49-13](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/cfc3c4bb-f66b-4464-9ab3-0084531fdcca)

![Screenshot from 2023-06-08 09-10-27](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/e2da7d28-bf0e-4b19-9ef0-0c928ff902bf)

![Screenshot from 2023-06-08 09-58-16](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/6bc4845c-cfe4-463a-a4d5-910bbf65edc8)

![Screenshot from 2023-06-10 22-40-12](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/9d304b48-bd28-4167-88b8-cda3339ec861)

![Screenshot from 2023-06-20 20-44-34](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/dac4ee44-d3f4-441f-b6c4-61f62b4bea46)

## Extra
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/b3a63bac-7ea2-485a-b3f1-d237d5b0906d)
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/c4fb1a4e-993f-4c62-8933-d333293b1a31)
![Screenshot from 2023-07-20 18-46-12](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/54f44971-0e47-46cc-94c6-c59c78336511)

# Hardware Debug Doc
## NORMAL RUN
![from_reset](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/174fdacb-a00b-423b-aac4-a79357dd0473)

![start_of_state_calibrate](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/f3e5dd2b-29fc-4171-81e2-46405c19060b)

![cntvalue_increments_until_end](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/9ea62c22-cc7d-497c-9136-8d9a14a3e966)

![first_mpr](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/00273821-0cb6-421f-adc2-4be436404b60)

![mpr_2](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/f7235f96-62b3-416a-9906-729c0d421e76)

![mpr_3](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/a9f08c05-5e0c-437a-9888-47cb43298037)

![mpr_4](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/67237f35-be2f-484b-9bbc-7d69fcf95aea)

## Increment CNTVALUE Indefinitely
![cntvalue_increments_continuously](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/0fce42ff-b73e-482a-ab5a-49126013f6c8)

![mpr_1_increments_continuously](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/f1f611b0-cfc0-4455-b2ae-5b1d41fedfcf)

![mpr_2_increments_continuously](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/6c85d8c0-afdb-4c46-abfc-7e15c9393bb0)

![mpr_3_increments_continuously](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/cdd57fb9-968f-43cf-9dfa-0a95be43280c)

![mpr_4_increments_continuously](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/fe3a7617-243b-4210-b247-89c3814c0f25)

![mpr_5_increments_continuously](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/d918daf7-cd8e-49bf-b378-ee6c86b2dc56)

![mpr_6_increments_continuously](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/d7da0993-6021-4b19-ab73-a7b2e85fec42)

![mpr_7_increments_continuously](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/875c5e91-30ca-4e7e-9312-28876f5eb9e5)






