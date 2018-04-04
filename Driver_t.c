void main(void){
	int COMPort;
	int buffer[200];
	int pointerBuffer;
	int endPointer;
	int temp1;
	int temp2;
	int temp3;
	int i;
	i = 0;
	while(i == 0){
		temp1 = 65497;/*IO_DATA_VERIFY_IN*/
		if (temp1 == 1){
			temp1 = 65496;/*IO_DATA_GET_INPUT*/
			buffer[endPointer] = temp1;
			temp3 = endPointer;
			endPointer = endPointer + 1;
			if(endPointer == 200){
				endPointer = 0;
			}
			if(COMPort == 0){
				temp2 = 3;
				temp2 = temp2 + temp3;
				temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (buffer)*/
				temp3 = endPointer;
				temp2 = 807;
				temp1 = 65522;/*STORE_DIRECTLY temp3 temp2 (buffer)*/
			}else{
				if(COMPort == 1){
					temp2 = 203;
					temp2 = temp2 + temp3;
					temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (buffer)*/
					temp3 = endPointer;
					temp2 = 808;
					temp1 = 65522;/*STORE_DIRECTLY temp3 temp2 (buffer)*/
				}else{
					if(COMPort == 2){
						temp2 = 403;
						temp2 = temp2 + temp3;
						temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (buffer)*/
						temp3 = endPointer;
						temp2 = 809;
						temp1 = 65522;/*STORE_DIRECTLY temp3 temp2 (buffer)*/
					}else{
						if(COMPort == 3){
							temp2 = 603;
							temp2 = temp2 + temp3;
							temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (buffer)*/
							temp3 = endPointer;
							temp2 = 810;
							temp1 = 65522;/*STORE_DIRECTLY temp3 temp2 (buffer)*/
						}
					}
				}
			}
		}
	}
}
