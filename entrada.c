void main(void){
	int systemCall;
	int value1SysCall;
	int value2SysCall;
	int buffer1[200];
	int buffer2[200];
	int buffer3[200];
	int buffer4[200];
	int pointerBuffer1;
	int pointerBuffer2;
	int pointerBuffer3;
	int pointerBuffer4;
	int endPointerBuffer1;
	int endPointerBuffer2;
	int endPointerBuffer3;
	int endPointerBuffer4;
	int ProcessList[50];/*Lista processos começando do zero, até EndList. Essa lista é a estrutura do escalonador.*/
	int ActualProcess;/*Processo atual em execução na CPU */
	int EndList;/*Fim da lista*/
	int Process[50];/*Cada indice é um PID, se o processo estiver em execução então vetor[PID] = 1;*/
	int ProcessUID[50];/*Cada indice é um PID, e vetor[PID] = ID do usuario*/
	int ProcessDate[50];/*Cada indice é um PID, e vetor[PID] = data no qual o processo foi criado(em nivel de software)*/
	int ProcessHora[50];/*Cada indice é um PID, e vetor[PID] = hora no qual o processo foi criado(em nivel de software)*/
	int ProcessPriority[50];/*Cada indice é um PID, e vetor[PID] = prioridade de 0 a 5*/
	int ProcessInitialPos[50];/*Cada indice é um PID, e vetor[PID] = Pagina IM onde inicia o processo.*/
	int ProcessLasPC[50];/*Cada indice é um PID, e vetor[PID] = ultimo PC executado na CPU.*/
	int ProcessSize[50];/*Cada indice é um PID, e vetor[PID] = tamanho do programa na memoria de instruções*/
	int ProcessLimitPC[50];/*Cada indice é um PID, e vetor[PID] = limite da execução do processo*/
	int ProcessMemPos[50];/*Pagina da memoria de dados onde inicia o processo.*/
	int ProcessFATLocation[50];/*Vetor de Posição da FAT onde está localizado o processo inidcado.*/
	int Nome[50];
	int ProcessoTopo;
	int TimeSlice;
	int FATType[300];
	int FATDate[300];
	int FATHour[300];
	int FATAttr[300];
	int FATCluster[300];
	int FATSize[300];
	int FATNome[300];
	int FATLoaded[300];
	int SizePagRAM;
	int SizePagIM;
	int QtdPagRAM;
	int QtdPagIM;
	int SizeMemSO;
	int SizeIMSO;
	int RAMPages[93];
	int IMPages[163];
	int TMR0Clock;
	int TMR0Status;
	int TMR0Register;
	int InterruptVector;
	int ComPort;
	int Driver[4];
	int COMType[4];
	int COMNome[4];
	int oldComPort;
	int i;
	int j;
	int temp1;
	int temp2;
	int temp3;
	int temp4;
	int temp5;
	int temp6;
	int temp7;
	int temp8;
	int temp9;
	int temp10;
	int temp11;
	int temp12;
	int temp13;
	int FATBeginRAM;	
	int bufferingbash;
	temp1 = 65510;/*SET_TYPE*/
	SizePagRAM = 700;
	SizePagIM = 400;
	QtdPagRAM = 93;
	QtdPagIM = 163;
	SizeMemSO = 6;/*colocar o tamanho em paginas de RAM do SO*/
	SizeIMSO = 105;/*colocar o tamanho em paginas de IM do SO*/
	i = 0;
	while(i<SizeMemSO){
		RAMPages[i] = 1;
		i = i + 1;
	}
	i = 0;
	while(i<SizeIMSO){
		IMPages[i] = 1;
		i = i + 1;
	}
	FATBeginRAM = 0;/*colocar aonde começa a fat na memoria.*/
	TimeSlice = 1000;/*time slice em ciclos de clock*/
	ActualProcess = 0;
	InterruptVector = 0;
	EndList = 0;
	
	/*CARREGAR FAT DO DISCO PARA AS VARIAVEIS*/
	temp1 = 1;
	temp2 = 2100;
	temp3 = 1465;
	temp3 = 65534;/*HD_LOAD_RAM(temp1, temp2, temp3)//HD_LOAD(cluster inicial, quantidade em posições de memoria, pagina da memoria);*/
	temp1 = 1;
	temp2 = 2100;
	FATBeginRAM = 0;	
	
	temp3 = 65533;/*SET_INT_PC*/
	/*Search for bash 66*/
	i = 0;
	temp1 = 301;
	while (i<300){
		if (FATNome[i] == 66){
			temp1 = i;
			i = 300;
		}else{
			i = i +1;
		}
	}
	
	if (temp1 == 301){
		/*retorna erro de que não foi encontrado arquivo com o nome - 1*/
	}else{
		if (FATType[temp1] == 0){
			/*retorna erro de que não existe um processo com o mesmo nome - 2*/
		}else{
			i = 0;
			while(i<50){
				if(Process[i] == 0){
					temp5 = i;
					i = 50;
				}else{
					temp5 = 51;
					i = i + 1;
				}
			}
			if (temp5 == 51){
				/*retorna erro de que não pode se executar processos ainda*/
			}else{
				temp2 = FATSize[temp1];
				temp2 = temp2/SizePagIM;
				temp2 = temp2 + 1;
				
				i = SizeIMSO;
				while(i<QtdPagIM){
					if (IMPages[i]==0){
						j = 0;
						temp3 = temp2 + 1;
						while (j<temp2){
							temp4 = i + j;
							if (IMPages[temp4]==1){
								j = temp3;
							}else{
								j = j + 1;
							}
						}
						if (j != temp3){
							temp3 = i;
							i = QtdPagIM;
						}else{
							temp3 = 0;
							i = i + 1;
						}
					}else{
						temp3 = 0;
						i = i + 1;
					}
				}
				if(temp3 == 0){
					/*solta erro de que não há espaço livre para rodar o processo*/
				}else{
					i = SizeMemSO;
					while(i<QtdPagRAM){
						if (RAMPages[i]==0){
							temp6 = i;
							RAMPages[i] = 1;
							i = QtdPagRAM;
						}else{
							temp6 = 0;
							i = i + 1;
						}
					}
					if (temp6 == 0){
						/*solta erro de que não há espaço livre na memória para rodar o processo*/
					}else{
						i = 0;
						while(i<temp2){
							temp4 = temp3+i;
							IMPages[temp4] = 1;
							i = i+1;
						}
						ProcessList[EndList] = temp5;
						EndList = EndList+1;
						Process[temp5] = 1;
						ProcessUID[temp5] = 0;
						ProcessDate[temp5] = 0;
						ProcessHora[temp5] = 0;
						ProcessPriority[temp5] = 2;
						ProcessInitialPos[temp5] = temp3;
						ProcessLasPC[temp5] = 0;
						ProcessSize[temp5] = FATSize[temp1];
						ProcessMemPos[temp5] = temp6;
						ProcessFATLocation[temp5] = temp1;
						Nome[temp5] = FATNome[temp1];
						temp2 = FATSize[temp1];
						temp4 = temp3*SizePagIM;
						temp4 = temp4 + temp2;
						ProcessLimitPC[temp5] = temp4;
						temp4 = FATCluster[temp1];
						temp3 = temp3*SizePagIM;
						temp4 = 65528;/*HD_LOAD_IM(temp4, temp2, temp3)//HD_LOAD(cluster inicial, quantidade em posições de memoria, posição de memoria);*/
						FATLoaded[temp1] = 1;
						
						temp2 = ProcessMemPos[temp5];
						temp2 = temp2*SizePagRAM;
						i = 0;
						temp3 = 65522;/*STORE_DIRECTLY i temp2 (last pc = 0)*/
						temp2 = temp2 + 1;
						temp3 = temp2+128;
						
						temp1 = ProcessInitialPos[temp5];
						temp1 = temp1*SizePagIM;
						temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (stack[0] = 0)*/
						temp2 = temp2 + 1;
						
						while(temp2<temp3){
							i = 0;
							temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack = 0)*/
							temp2 = temp2 + 1;
						}
						
						temp3 = temp2+128;
						
						temp1 = ProcessMemPos[temp5];
						temp1 = temp1*SizePagRAM;
						temp1 = temp1+299;
						temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (stack[0] = 0)*/
						temp2 = temp2 + 1;
						
						while(temp2<temp3){
							i = 0;
							temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack = 0)*/
							temp2 = temp2 + 1;
						}
						i = 0;
						temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack_ptr = 0)*/
						temp2 = temp2 + 1;
						i = 0;
						temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack_ptr = 0)*/
						temp2 = temp2 + 1;
						temp3 = temp2 + 40;
						while(temp2<temp3){
							i = 0;
							temp1 = 65522;/*STORE_DIRECTLY i temp2 (register_bank = 0)*/
							temp2 = temp2 + 1;
						}
					}
				}
			}
		}
	}
	ProcessoTopo = temp5;
	bufferingbash = 0;
	/*Carregar os drivers*/
	temp1 = 65504;/*GET_COM temp1*/
	ComPort = temp1;
	temp7 = ComPort;
	oldComPort = temp7;
	while(temp7!=0){
		if (temp7 >= 8){
			temp8 = 8;
			temp9 = 3;
		}else{
			if (temp7 >= 4){
				temp8 = 4;
				temp9 = 2;
			}else{
				if(temp7 >= 2){
					temp8 = 2;
					temp9 = 1;
				}else{
					if(temp7 >= 1){
						temp8 = 1;
						temp9 = 0;
					}
				}
			}
		}
		/*Search for driver*/
		
		temp1 = 65505; /*GET_COM_N temp9 temp1;*/
		temp9 = temp9;
		COMNome[temp9] = temp1;
		temp1 = 65503; /*GET_COM_TYPE temp9 temp1;*/
		temp9 = temp9;
		COMType[temp9] = temp1;
		
		i = 0;
		while (i<300){
			if (FATNome[i] == COMNome[temp9]){
				temp1 = i;
				i = 300;
			}else{
				temp1 = 301;
				i = i +1;
			}
		}
		
		if (temp1 == 301){
			/*retorna erro de que não foi encontrado arquivo com o nome*/
			COMNome[temp9] = 0;
			COMType[temp9] = 0;
		}else{
			if (FATType[temp1] == 1){
				/*retorna erro de que não existe um processo com o mesmo nome*/
				COMNome[temp9] = 0;
				COMType[temp9] = 0;
			}else{
				i = 0;
				while(i<50){
					if(Process[i] == 0){
						temp5 = i;
						i = 50;
					}else{
						temp5 = 51;
						i = i + 1;
					}
				}
				if (temp5 == 51){
					/*retorna erro de que não pode-se executar processos ainda*/
					COMNome[temp9] = 0;
					COMType[temp9] = 0;
				}else{
					temp2 = FATSize[temp1];
					temp2 = temp2/SizePagIM;
					temp2 = temp2 + 1;
					
					i = SizeIMSO;
					while(i<QtdPagIM){
						if (IMPages[i]==0){
							j = 0;
							temp3 = temp2 + 1;
							while (j<temp2){
								temp4 = i + j;
								if (IMPages[temp4]==1){
									j = temp3;
								}else{
									j = j + 1;
								}
							}
							if (j != temp3){
								temp3 = i;
								i = QtdPagIM;
							}else{
								temp3 = 0;
								i = i + 1;
							}
						}else{
							temp3 = 0;
							i = i + 1;
						}
					}
					if(temp3 == 0){
						/*solta erro de que não há espaço livre para rodar o processo*/
						COMNome[temp9] = 0;
						COMType[temp9] = 0;
					}else{
						i = SizeMemSO;
						while(i<QtdPagRAM){
							if (RAMPages[i]==0){
								temp6 = i;
								RAMPages[i] = 1;
								i = QtdPagRAM;
							}else{
								temp6 = 0;
								i = i + 1;
							}
						}
						if (temp6 == 0){
							/*solta erro de que não há espaço livre na memória para rodar o processo*/
							COMNome[temp9] = 0;
							COMType[temp9] = 0;
						}else{
							i = 0;
							while(i<temp2){
								temp4 = temp3+i;
								IMPages[temp4] = 1;
								i = i+1;
							}
							ProcessList[EndList] = temp5;
							EndList = EndList+1;
							Process[temp5] = 1;
							ProcessUID[temp5] = 0;
							ProcessDate[temp5] = 0;
							ProcessHora[temp5] = 0;
							ProcessPriority[temp5] = 2;
							ProcessInitialPos[temp5] = temp3;
							ProcessLasPC[temp5] = 0;
							ProcessSize[temp5] = FATSize[temp1];
							ProcessMemPos[temp5] = temp6;
							ProcessFATLocation[temp5] = temp1;
							Nome[temp5] = FATNome[temp1];
							temp2 = FATSize[temp1];
							temp4 = temp3*SizePagIM;
							temp4 = temp4 + temp2;
							ProcessLimitPC[temp5] = temp4;
							temp4 = FATCluster[temp1];
							temp3 = temp3*SizePagIM;
							temp4 = 65528;/*HD_LOAD_IM(temp4, temp2, temp3)//HD_LOAD(cluster inicial, quantidade em posições de memoria, posição de memoria);*/
							FATLoaded[temp1] = 1;
							Driver[temp9] = temp5;
														
							temp2 = ProcessMemPos[temp5];
							temp2 = temp2*SizePagRAM;
							i = 0;
							temp3 = 65522;/*STORE_DIRECTLY i temp2 (last pc = 0)*/
							temp2 = temp2 + 1;
							temp3 = temp2+128;
							
							temp1 = ProcessInitialPos[temp5];
							temp1 = temp1*SizePagIM;
							temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (stack[0] = 0)*/
							temp2 = temp2 + 1;
							while(temp2<temp3){
								i = 0;
								temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack = 0)*/
								temp2 = temp2 + 1;
							}
							temp3 = temp2+128;
							
							temp1 = ProcessMemPos[temp5];
							temp1 = temp1*SizePagRAM;
							temp1 = temp1+299;
							temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (stack[0] = 0)*/
							temp2 = temp2 + 1;
							while(temp2<temp3){
								i = 0;
								temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack = 0)*/
								temp2 = temp2 + 1;
							}
							i = 0;
							temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack_ptr = 0)*/
							temp2 = temp2 + 1;
							i = 0;
							temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack_ptr = 0)*/
							temp2 = temp2 + 1;
							temp3 = temp2 + 40;
							while(temp2<temp3){
								i = 0;
								temp1 = 65522;/*STORE_DIRECTLY i temp2 (register_bank = 0)*/
								temp2 = temp2 + 1;
							}
							temp9 = temp9;
							temp1 = 65522;/*STORE_DIRECTLY temp9 temp2 (Comport = temp9)*/
						}
					}
				}
			}
		}
		temp7 = temp7 - temp8;
	}
	
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------Inicializa o escalonador------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	TMR0Clock = 50000000;
	TMR0Status = 1;
	TMR0Register = TimeSlice;
	temp1 = TMR0Register;
	temp1 = 65502; /*ACT_TMR temp1*/
	
	temp11 = ProcessList[ActualProcess];
										
	/*Carrega as pilhas*/
	temp2 = ProcessMemPos[temp11];
	temp2 = temp2*SizePagRAM;
	temp2 = temp2 + 1;
	temp3 = temp2+128;
	i = 0;
	while(temp2<temp3){
		temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
		temp2 = temp2 + 1;
		i = i+1;
	}
	temp3 = temp2+128;
	i = 0;
	while(temp2<temp3){
		temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
		temp2 = temp2 + 1;
		i = i+1;
	}
	temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
	temp2 = temp2 + 1;
	temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
	temp2 = temp2 + 1;
	temp2 = temp2 + 7;

	temp4 = ProcessLasPC[temp11];
	temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/

	temp2 = temp2 + 1;
	temp2 = temp2 + 32;

	temp1 = 65511; /*SET_MEM_BEG 0 temp2*/

	temp2 = ProcessLimitPC[temp11];
	temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/

	temp2 = ProcessMemPos[temp11];
	temp2 = temp2 + 1;
	temp2 = temp2*SizePagRAM;
	temp2 = temp2 - 1;
	temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
	i = 1;if(i==0){i = 1;}
	
	temp1 = InterruptVector;
	temp1 = 65506;/*SAVE_INT temp1*/
	temp1 = 65513;/*MEM_TO_REG*/
	temp1 = 65512; /*JMP_REGISTER $7*/
	
	
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*---------rotina de interrupção/escalonador----------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	/*----------------------------------------------------*/
	i = 1;if(i==0){i = 1;}
	
	temp1 = 65516;/*SET_LIM_PC 65536*/
	
	temp1 = 65515;/*SET_LIM_MEM 65536*/
	/*coloca dois pois SETA O LIMITE EM 65536*/
	
	temp1 = 65527;/*GET_LAST_PC temp1*/
	temp11 = ProcessList[ActualProcess];
	ProcessLasPC[temp11] = temp1;
	
	/*salva a pilha*/
	temp2 = ProcessMemPos[temp11];
	temp2 = temp2*SizePagRAM;
	temp3 = 65522;/*STORE_DIRECTLY temp1 temp2 (Salva o last pc)*/
	temp2 = temp2 + 1;
	temp3 = temp2+128;
	i = 0;
	while(temp2<temp3){
		temp1 = 65526;/*STORE_STACK_R 0 temp2 i */
		temp2 = temp2 + 1;
		i = i+1;
	}
	temp3 = temp2+128;
	i = 0;
	while(temp2<temp3){
		temp1 = 65525;/*STORE_STACK_PC 0 temp2 i*/
		temp2 = temp2 + 1;
		i = i+1;
	}
	temp1 = 65524;/*STORE_PTR_R 0 temp2*/
	temp2 = temp2 + 1;
	temp1 = 65523;/*STORE_PTR_PC 0 temp2*/
	temp2 = temp2 + 1;
	
	temp1 = 65507;/*GET_INT 0 0 temp1*/
	InterruptVector = temp1;
	
	/*verifica o vetor de interrupção*/
	if (InterruptVector>=16){
		
		InterruptVector = InterruptVector - 16;
		temp1 = 65500;/*SYSCALL_DATA_LOAD (TIPO) temp1*/
		systemCall = temp1;
		temp1 = 65499;/*SYSCALL_DATA_LOAD (VALUE1) temp1*/
		value1SysCall = temp1;
		temp1 = 65498;/*SYSCALL_DATA_LOAD (VALUE2) temp1*/
		value2SysCall = temp1;
		if (systemCall==1){
			temp4 = 0;
			i = 0;
			if(temp11 != 0){/*se nao for o bash*/
				if (bufferingbash != 1){/*e se nao estive no buffer o bash*/
					while(i < 4){
						if (value2SysCall == COMType[i]){
							if(i == 0){
								temp10 = endPointerBuffer1;
								temp12 = pointerBuffer1;
								temp13 = buffer1[temp12];
							}else{
								if(i == 1){
									temp10 = endPointerBuffer2;
									temp12 = pointerBuffer2;
									temp13 = buffer2[temp12];
								}else{
									if(i == 2){
										temp10 = endPointerBuffer3;
										temp12 = pointerBuffer3;
										temp13 = buffer3[temp12];
									}else{
										if(i == 3){
											temp10 = endPointerBuffer4;
											temp12 = pointerBuffer4;
											temp13 = buffer4[temp12];
										}
									}
								}
							}
							if (temp12 != temp10){
								if (temp12 == 199){
									temp12 = 0;
								}else{
									temp12 = temp12 + 1;
								}
								temp9 = Driver[i];
								temp8 = ProcessMemPos[temp9];
								temp8 = temp8*SizePagRAM;
								temp8 = temp8 + 1;
								temp8 = temp8 + 128;
								temp8 = temp8 + 128;
								temp8 = temp8 + 1;
								temp8 = temp8 + 40;
								temp8 = temp8 + 1;
								temp8 = temp8 + 200;
								temp12 = temp12 + 0;
								temp1 = 65522;/*STORE_DIRECTLY temp12 temp8 (atualiza o apontador no driver)*/
								if(i == 0){
									pointerBuffer1 = temp12;
								}else{
									if(i == 1){
										pointerBuffer2 = temp12;
									}else{
										if(i == 2){
											pointerBuffer3 = temp12;
										}else{
											if(i == 3){
												pointerBuffer4 = temp12;
											}
										}
									}
								}
								i = 4;
							}else{
								/*retorna 0*/
								temp13 = 0;
							}
							temp13 = temp13 + 0;
							temp2 = temp2 + value1SysCall;
							temp1 = 65522;/*STORE_DIRECTLY temp13 temp2 (salva o input direto no registrador do contexto em questão)*/
							temp13 = temp13;
							temp4 = 1;
						}
						i = i + 1;
					}
				}
			}else{
				while(i < 4){
					if (value2SysCall == COMType[i]){
						if(i == 0){
							temp10 = endPointerBuffer1;
							temp12 = pointerBuffer1;
							temp13 = buffer1[temp12];
						}else{
							if(i == 1){
								temp10 = endPointerBuffer2;
								temp12 = pointerBuffer2;
								temp13 = buffer2[temp12];
							}else{
								if(i == 2){
									temp10 = endPointerBuffer3;
									temp12 = pointerBuffer3;
									temp13 = buffer3[temp12];
								}else{
									if(i == 3){
										temp10 = endPointerBuffer4;
										temp12 = pointerBuffer4;
										temp13 = buffer4[temp12];
									}
								}
							}
						}
						if (temp12 != temp10){
							if (temp12 == 199){
								temp12 = 0;
							}else{
								temp12 = temp12 + 1;
							}
							temp9 = Driver[i];
							temp8 = ProcessMemPos[temp9];
							temp8 = temp8*SizePagRAM;
							temp8 = temp8 + 1;
							temp8 = temp8 + 128;
							temp8 = temp8 + 128;
							temp8 = temp8 + 1;
							temp8 = temp8 + 40;
							temp8 = temp8 + 1;
							temp8 = temp8 + 200;
							temp12 = temp12 + 0;
							temp1 = 65522;/*STORE_DIRECTLY temp12 temp8 (atualiza o apontador no driver)*/
							if(i == 0){
								pointerBuffer1 = temp12;
							}else{
								if(i == 1){
									pointerBuffer2 = temp12;
								}else{
									if(i == 2){
										pointerBuffer3 = temp12;
									}else{
										if(i == 3){
											pointerBuffer4 = temp12;
										}
									}
								}
							}
							i = 4;
						}else{
							/*retorna 0*/
							temp13 = 0;
						}
						temp13 = temp13 + 0;
						temp2 = temp2 + value1SysCall;
						temp1 = 65522;/*STORE_DIRECTLY temp13 temp2 (salva o input direto no registrador do contexto em questão)*/
						temp13 = temp13;
						temp4 = 1;
					}
					i = i + 1;
				}
			}
			
			/*vai para o proximo processo*/
			if (temp4 == 1){/*atualiza o PC do processo que fez a chamada de sistema pois achou um dispositivo e pegou a entrada.*/
				temp4 = ProcessLasPC[temp11];
				temp4 = temp4 + 1;
				ProcessLasPC[temp11] = temp4;
			}
			
			temp13 = ActualProcess + 1;
			if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
				ActualProcess = temp13;
			}else{
				ActualProcess = 0;
			}
			temp11 = ProcessList[ActualProcess];
			
			/*Carrega as pilhas*/
			temp2 = ProcessMemPos[temp11];
			temp2 = temp2*SizePagRAM;
			temp2 = temp2 + 1;
			temp3 = temp2+128;
			i = 0;
			while(temp2<temp3){
				temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
				temp2 = temp2 + 1;
				i = i+1;
			}
			temp3 = temp2+128;
			i = 0;
			while(temp2<temp3){
				temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
				temp2 = temp2 + 1;
				i = i+1;
			}
			temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
			temp2 = temp2 + 1;
			temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
			temp2 = temp2 + 1;
			temp2 = temp2 + 7;
			
			temp4 = ProcessLasPC[temp11];
			temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
			
			temp2 = temp2 + 1;
			temp2 = temp2 + 32;
			
			temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
			
			temp2 = ProcessLimitPC[temp11];
			temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
			
			temp2 = ProcessMemPos[temp11];
			temp2 = temp2 + 1;
			temp2 = temp2*SizePagRAM;
			temp2 = temp2 - 1;
			temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
			i = 1;if(i==0){i = 1;}/*salva todos os registradores na memoria do SO*/
			
			temp1 = InterruptVector;
			temp1 = 65506;/*SAVE_INT temp1*/
			temp1 = 65513;/*MEM_TO_REG*/
			temp1 = 65512; /*JMP_REGISTER $7*/
		}else{
			if (systemCall==2){
				i = 0;
				temp4 = 0;
				if(temp11 != 0){/*se nao for o bash*/
					if (bufferingbash != 1){/*e se nao estive no buffer o bash*/
						while(i < 4){
							if (value2SysCall == COMType[i]){
								if(i == 0){
									temp10 = endPointerBuffer1;
									temp12 = pointerBuffer1;
								}else{
									if(i == 1){
										temp10 = endPointerBuffer2;
										temp12 = pointerBuffer2;
									}else{
										if(i == 2){
											temp10 = endPointerBuffer3;
											temp12 = pointerBuffer3;
										}else{
											if(i == 3){
												temp10 = endPointerBuffer4;
												temp12 = pointerBuffer4;
											}
										}
									}
								}
								if (temp10 == 199){
									temp10 = 0;
								}else{
									temp10 = temp10 + 1;
								}
								
								if (temp10!=temp12){
									temp9 = Driver[i];
									temp8 = ProcessMemPos[temp9];
									temp8 = temp8*SizePagRAM;
									temp8 = temp8 + 1;
									temp8 = temp8 + 128;
									temp8 = temp8 + 128;
									temp8 = temp8 + 1;
									temp8 = temp8 + 40;
									temp8 = temp8 + 1;
									temp8 = temp8 + 200;
									temp8 = temp8 + 1;
									temp10 = temp10 + 0;
									temp1 = 65522;/*STORE_DIRECTLY temp10 temp8 (atualiza o apontador no driver)*/
									
									if(i == 0){
										endPointerBuffer1 = temp10;
										if (temp10 == 0){
											temp10 = 199;
										}else{
											temp10 = temp10 - 1;
										}
										buffer1[temp10] = value1SysCall;
									}else{
										if(i == 1){
											endPointerBuffer2 = temp10;
											if (temp10 == 0){
												temp10 = 199;
											}else{
												temp10 = temp10 - 1;
											}
											buffer2[temp10] = value1SysCall;
										}else{
											if(i == 2){
												endPointerBuffer3 = temp10;
												if (temp10 == 0){
													temp10 = 199;
												}else{
													temp10 = temp10 - 1;
												}
												buffer3[temp10] = value1SysCall;
											}else{
												if(i == 3){
													endPointerBuffer4 = temp10;
													if (temp10 == 0){
														temp10 = 199;
													}else{
														temp10 = temp10 - 1;
													}
													buffer4[temp10] = value1SysCall;
												}
											}
										}
									}
									i = 4;
									temp8 = ProcessMemPos[temp9];
									temp8 = temp8*SizePagRAM;
									temp8 = temp8 + 1;
									temp8 = temp8 + 128;
									temp8 = temp8 + 128;
									temp8 = temp8 + 1;
									temp8 = temp8 + 40;
									temp8 = temp8 + 1;
									temp8 = temp8 + temp10;
									temp1 = 65522;/*STORE_DIRECTLY value1SysCall temp8 (salva no buffer do driver)*/
									value1SysCall = value1SysCall + 0;
									temp8 = temp8 + 0;
									temp4 = 1;
								}						
							}
							i = i + 1;
						}
					}
				}else{
					while(i < 4){
						if (value2SysCall == COMType[i]){
							if(i == 0){
								temp10 = endPointerBuffer1;
								temp12 = pointerBuffer1;
							}else{
								if(i == 1){
									temp10 = endPointerBuffer2;
									temp12 = pointerBuffer2;
								}else{
									if(i == 2){
										temp10 = endPointerBuffer3;
										temp12 = pointerBuffer3;
									}else{
										if(i == 3){
											temp10 = endPointerBuffer4;
											temp12 = pointerBuffer4;
										}
									}
								}
							}
							if (temp10 == 199){
								temp10 = 0;
							}else{
								temp10 = temp10 + 1;
							}
							
							if (temp10!=temp12){
								temp9 = Driver[i];
								temp8 = ProcessMemPos[temp9];
								temp8 = temp8*SizePagRAM;
								temp8 = temp8 + 1;
								temp8 = temp8 + 128;
								temp8 = temp8 + 128;
								temp8 = temp8 + 1;
								temp8 = temp8 + 40;
								temp8 = temp8 + 1;
								temp8 = temp8 + 200;
								temp8 = temp8 + 1;
								temp10 = temp10 + 0;
								temp1 = 65522;/*STORE_DIRECTLY temp10 temp8 (atualiza o apontador no driver)*/
								
								if(i == 0){
									endPointerBuffer1 = temp10;
									if (temp10 == 0){
										temp10 = 199;
									}else{
										temp10 = temp10 - 1;
									}
									buffer1[temp10] = value1SysCall;
								}else{
									if(i == 1){
										endPointerBuffer2 = temp10;
										if (temp10 == 0){
											temp10 = 199;
										}else{
											temp10 = temp10 - 1;
										}
										buffer2[temp10] = value1SysCall;
									}else{
										if(i == 2){
											endPointerBuffer3 = temp10;
											if (temp10 == 0){
												temp10 = 199;
											}else{
												temp10 = temp10 - 1;
											}
											buffer3[temp10] = value1SysCall;
										}else{
											if(i == 3){
												endPointerBuffer4 = temp10;
												if (temp10 == 0){
													temp10 = 199;
												}else{
													temp10 = temp10 - 1;
												}
												buffer4[temp10] = value1SysCall;
											}
										}
									}
								}
								i = 4;
								temp8 = ProcessMemPos[temp9];
								temp8 = temp8*SizePagRAM;
								temp8 = temp8 + 1;
								temp8 = temp8 + 128;
								temp8 = temp8 + 128;
								temp8 = temp8 + 1;
								temp8 = temp8 + 40;
								temp8 = temp8 + 1;
								temp8 = temp8 + temp10;
								temp1 = 65522;/*STORE_DIRECTLY value1SysCall temp8 (salva no buffer do driver)*/
								value1SysCall = value1SysCall + 0;
								temp8 = temp8 + 0;
								temp4 = 1;
							}						
						}
						i = i + 1;
					}
				}
				/*vai para o proximo processo*/
				if (temp4 == 1){
					temp4 = ProcessLasPC[temp11];
					temp4 = temp4 + 1;
					ProcessLasPC[temp11] = temp4;
				}
				
				temp13 = ActualProcess + 1;
				
				if(ActualProcess<EndList){
					ActualProcess = temp13;
				}else{
					ActualProcess = 0;
				}
				temp11 = ProcessList[ActualProcess];
				
				/*Carrega as pilhas*/
				temp2 = ProcessMemPos[temp11];
				temp2 = temp2*SizePagRAM;
				temp2 = temp2 + 1;
				temp3 = temp2+128;
				i = 0;
				while(temp2<temp3){
					temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
					temp2 = temp2 + 1;
					i = i+1;
				}
				temp3 = temp2+128;
				i = 0;
				while(temp2<temp3){
					temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
					temp2 = temp2 + 1;
					i = i+1;
				}
				temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
				temp2 = temp2 + 1;
				temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
				temp2 = temp2 + 1;
				temp2 = temp2 + 7;
				
				temp4 = ProcessLasPC[temp11];
				temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
				
				temp2 = temp2 + 1;
				temp2 = temp2 + 32;
				
				temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
				
				temp2 = ProcessLimitPC[temp11];
				temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
				
				temp2 = ProcessMemPos[temp11];
				temp2 = temp2 + 1;
				temp2 = temp2*SizePagRAM;
				temp2 = temp2 - 1;
				temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
				i = 1;if(i==0){i = 1;}
				temp1 = InterruptVector;
				temp1 = 65506;/*SAVE_INT temp1*/
				temp1 = 65513;/*MEM_TO_REG*/
				temp1 = 65512; /*JMP_REGISTER $7*/
				
			}else{
				if (systemCall == 3){/*kill*/
					temp11 = 51;
					i = 0;
					while (i < EndList){
						temp13 = ProcessList[i];
						temp12 = Nome[temp13];
						if (temp12 == value1SysCall){
							temp11 = i;
							i = EndList;
						}else{
							i = i + 1;
						}
					}
					if (temp11 == 51){
						/* Solta o erro de que não existe processo com o nome*/
						temp2 = temp2 + value2SysCall;
						temp1 = 65522;/*STORE_DIRECTLY 6 temp2 (salva o input direto no registrador do contexto em questão)*/
						
						temp11 = ProcessList[ActualProcess];
						temp4 = ProcessLasPC[temp11];
						temp4 = temp4 + 1;
						ProcessLasPC[temp11] = temp4;
						
						temp13 = ActualProcess + 1;
						if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
							ActualProcess = temp13;
						}else{
							ActualProcess = 0;
						}
						
						temp11 = ProcessList[ActualProcess];
												
						/*Carrega as pilhas*/
						temp2 = ProcessMemPos[temp11];
						temp2 = temp2*SizePagRAM;
						temp2 = temp2 + 1;
						temp3 = temp2+128;
						i = 0;
						while(temp2<temp3){
							temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
							temp2 = temp2 + 1;
							i = i+1;
						}
						temp3 = temp2+128;
						i = 0;
						while(temp2<temp3){
							temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
							temp2 = temp2 + 1;
							i = i+1;
						}
						temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
						temp2 = temp2 + 1;
						temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
						temp2 = temp2 + 1;
						temp2 = temp2 + 7;
						
						temp4 = ProcessLasPC[temp11];
						temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
						
						temp2 = temp2 + 1;
						temp2 = temp2 + 32;
						
						temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
						
						temp2 = ProcessLimitPC[temp11];
						temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
						
						temp2 = ProcessMemPos[temp11];
						temp2 = temp2 + 1;
						temp2 = temp2*SizePagRAM;
						temp2 = temp2 - 1;
						temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
						i = 1;if(i==0){i = 1;}
						
						temp1 = InterruptVector;
						temp1 = 65506;/*SAVE_INT temp1*/
						temp1 = 65513;/*MEM_TO_REG*/
						temp1 = 65512; /*JMP_REGISTER $7*/
						
						/* Solta o erro de que não existe processo com o nome*/
					}else{
						temp2 = temp2 + value2SysCall;
						temp1 = 65522;/*STORE_DIRECTLY 0 temp2 (salva o input direto no registrador do contexto em questão)*/
						
						temp5 = ProcessList[temp11];
						temp1 = ProcessFATLocation[temp5];
						
						temp2 = ProcessSize[temp5];
						temp2 = temp2/SizePagIM;
						temp2 = temp2 + 1;
						
						temp3 = ProcessInitialPos[temp5];
						
						temp4 = temp3 + temp2;
						while(temp3<temp4){
							IMPages[temp3] = 0;
							temp3 = temp3 + 1;
						}
						
						ProcessInitialPos[temp5] = 0;
						
						temp3 = ProcessMemPos[temp5];
						RAMPages[temp3] = 0;
						
						ProcessMemPos[temp5] = 0;
						
						Process[temp5] = 0;
						
						EndList = EndList - 1;
						temp8 = temp11;
						while(temp11<EndList){
							temp10 = temp11 + 1;
							temp9 = ProcessList[temp10];
							ProcessList[temp11] = temp9;
							temp11 = temp10;
						}
						FATLoaded[temp1] = 0;
						
						if (ActualProcess > temp8){
							ActualProcess = ActualProcess - 1;
						}else{
							if (ActualProcess < temp8){
								ActualProcess = ActualProcess + 1;
							}else{
								ActualProcess = ActualProcess;
							}
						}
						
						
						temp11 = ProcessList[ActualProcess];
						
						/*Carrega as pilhas*/
						temp2 = ProcessMemPos[temp11];
						temp2 = temp2*SizePagRAM;
						temp2 = temp2 + 1;
						temp3 = temp2+128;
						i = 0;
						while(temp2<temp3){
							temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
							temp2 = temp2 + 1;
							i = i+1;
						}
						temp3 = temp2+128;
						i = 0;
						while(temp2<temp3){
							temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
							temp2 = temp2 + 1;
							i = i+1;
						}
						temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
						temp2 = temp2 + 1;
						temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
						temp2 = temp2 + 1;
						temp2 = temp2 + 7;
						
						temp4 = ProcessLasPC[temp11];
						temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
						
						temp2 = temp2 + 1;
						temp2 = temp2 + 32;
						
						temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
						
						temp2 = ProcessLimitPC[temp11];
						temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
						
						temp2 = ProcessMemPos[temp11];
						temp2 = temp2 + 1;
						temp2 = temp2*SizePagRAM;
						temp2 = temp2 - 1;
						temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
						i = 1;if(i==0){i = 1;}
						
						temp1 = InterruptVector;
						temp1 = 65506;/*SAVE_INT temp1*/
						temp1 = 65513;/*MEM_TO_REG*/
						temp1 = 65512; /*JMP_REGISTER $7*/
					}
				}else{
					if (systemCall == 4){/*run*/
						/*Search for process*/
						i = 0;
						temp1 = 301;
						while (i<300){
							if (FATNome[i] == value1SysCall){
								temp1 = i;
								i = 300;
							}else{
								i = i + 1;
							}
						}
						
						if (temp1 == 301){
							/*retorna erro de que não foi encontrado arquivo com o nome - 1*/
							
							temp11 = ProcessList[ActualProcess];
											
							temp2 = ProcessMemPos[temp11];
							temp2 = temp2*SizePagRAM;
							temp2 = temp2 + 1;
							temp2 = temp2+128;
							temp2 = temp2+128;
							temp2 = temp2 + 1;
							temp2 = temp2 + 1;
							/* Solta o erro de que não existe processo com o nome*/
							temp2 = temp2 + value2SysCall;
							temp1 = 65522;/*STORE_DIRECTLY 1 temp2 (salva o input direto no registrador do contexto em questão)*/
							
							temp4 = ProcessLasPC[temp11];
							temp4 = temp4 + 1;
							ProcessLasPC[temp11] = temp4;
							
							temp13 = ActualProcess + 1;
							if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
								ActualProcess = temp13;
							}else{
								ActualProcess = 0;
							}
							
							temp11 = ProcessList[ActualProcess];
													
							/*Carrega as pilhas*/
							temp2 = ProcessMemPos[temp11];
							temp2 = temp2*SizePagRAM;
							temp2 = temp2 + 1;
							temp3 = temp2+128;
							i = 0;
							while(temp2<temp3){
								temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
								temp2 = temp2 + 1;
								i = i+1;
							}
							temp3 = temp2+128;
							i = 0;
							while(temp2<temp3){
								temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
								temp2 = temp2 + 1;
								i = i+1;
							}
							temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
							temp2 = temp2 + 1;
							temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
							temp2 = temp2 + 1;
							temp2 = temp2 + 7;
							
							temp4 = ProcessLasPC[temp11];
							temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
							
							temp2 = temp2 + 1;
							temp2 = temp2 + 32;
							
							temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
							
							temp2 = ProcessLimitPC[temp11];
							temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
							
							temp2 = ProcessMemPos[temp11];
							temp2 = temp2 + 1;
							temp2 = temp2*SizePagRAM;
							temp2 = temp2 - 1;
							temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
							i = 1;if(i==0){i = 1;}
							
							temp1 = InterruptVector;
							temp1 = 65506;/*SAVE_INT temp1*/
							temp1 = 65513;/*MEM_TO_REG*/
							temp1 = 65512; /*JMP_REGISTER $7*/
						}else{
							if (FATType[temp1] == 0){
								/*retorna erro de que não existe um processo com o mesmo nome - 2*/
								
								temp11 = ProcessList[ActualProcess];
											
								temp2 = ProcessMemPos[temp11];
								temp2 = temp2*SizePagRAM;
								temp2 = temp2 + 1;
								temp2 = temp2+128;
								temp2 = temp2+128;
								temp2 = temp2 + 1;
								temp2 = temp2 + 1;
								/* Solta o erro de que não existe processo com o nome*/
								temp2 = temp2 + value2SysCall;
								temp1 = 65522;/*STORE_DIRECTLY 2 temp2 (salva o input direto no registrador do contexto em questão)*/
								
								temp4 = ProcessLasPC[temp11];
								temp4 = temp4 + 1;
								ProcessLasPC[temp11] = temp4;
								
								temp13 = ActualProcess + 1;
								if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
									ActualProcess = temp13;
								}else{
									ActualProcess = 0;
								}
								
								temp11 = ProcessList[ActualProcess];
														
								/*Carrega as pilhas*/
								temp2 = ProcessMemPos[temp11];
								temp2 = temp2*SizePagRAM;
								temp2 = temp2 + 1;
								temp3 = temp2+128;
								i = 0;
								while(temp2<temp3){
									temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
									temp2 = temp2 + 1;
									i = i+1;
								}
								temp3 = temp2+128;
								i = 0;
								while(temp2<temp3){
									temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
									temp2 = temp2 + 1;
									i = i+1;
								}
								temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
								temp2 = temp2 + 1;
								temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
								temp2 = temp2 + 1;
								temp2 = temp2 + 7;
								
								temp4 = ProcessLasPC[temp11];
								temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
								
								temp2 = temp2 + 1;
								temp2 = temp2 + 32;
								
								temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
								
								temp2 = ProcessLimitPC[temp11];
								temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
								
								temp2 = ProcessMemPos[temp11];
								temp2 = temp2 + 1;
								temp2 = temp2*SizePagRAM;
								temp2 = temp2 - 1;
								temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
								i = 1;if(i==0){i = 1;}
								
								temp1 = InterruptVector;
								temp1 = 65506;/*SAVE_INT temp1*/
								temp1 = 65513;/*MEM_TO_REG*/
								temp1 = 65512; /*JMP_REGISTER $7*/
							}else{
								i = 0;
								while(i<50){
									if(Process[i] == 0){
										temp5 = i;
										i = 50;
									}else{
										temp5 = 51;
										i = i + 1;
									}
								}
								if (temp5 == 51){
									/*retorna erro de que não pode se executar processos ainda - 3*/
									
									temp11 = ProcessList[ActualProcess];
											
									temp2 = ProcessMemPos[temp11];
									temp2 = temp2*SizePagRAM;
									temp2 = temp2 + 1;
									temp2 = temp2+128;
									temp2 = temp2+128;
									temp2 = temp2 + 1;
									temp2 = temp2 + 1;
									/* Solta o erro de que não existe processo com o nome*/
									temp2 = temp2 + value2SysCall;
									temp1 = 65522;/*STORE_DIRECTLY 3 temp2 (salva o input direto no registrador do contexto em questão)*/
									
									temp4 = ProcessLasPC[temp11];
									temp4 = temp4 + 1;
									ProcessLasPC[temp11] = temp4;
									
									temp13 = ActualProcess + 1;
									if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
										ActualProcess = temp13;
									}else{
										ActualProcess = 0;
									}
									
									temp11 = ProcessList[ActualProcess];
															
									/*Carrega as pilhas*/
									temp2 = ProcessMemPos[temp11];
									temp2 = temp2*SizePagRAM;
									temp2 = temp2 + 1;
									temp3 = temp2+128;
									i = 0;
									while(temp2<temp3){
										temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
										temp2 = temp2 + 1;
										i = i+1;
									}
									temp3 = temp2+128;
									i = 0;
									while(temp2<temp3){
										temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
										temp2 = temp2 + 1;
										i = i+1;
									}
									temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
									temp2 = temp2 + 1;
									temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
									temp2 = temp2 + 1;
									temp2 = temp2 + 7;
									
									temp4 = ProcessLasPC[temp11];
									temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
									
									temp2 = temp2 + 1;
									temp2 = temp2 + 32;
									
									temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
									
									temp2 = ProcessLimitPC[temp11];
									temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
									
									temp2 = ProcessMemPos[temp11];
									temp2 = temp2 + 1;
									temp2 = temp2*SizePagRAM;
									temp2 = temp2 - 1;
									temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
									i = 1;if(i==0){i = 1;}
									
									temp1 = InterruptVector;
									temp1 = 65506;/*SAVE_INT temp1*/
									temp1 = 65513;/*MEM_TO_REG*/
									temp1 = 65512; /*JMP_REGISTER $7*/
								}else{
									temp2 = FATSize[temp1];
									temp2 = temp2/SizePagIM;
									temp2 = temp2 + 1;
									
									i = SizeIMSO;
									while(i<QtdPagIM){
										if (IMPages[i]==0){
											j = 0;
											temp3 = temp2 + 1;
											while (j<temp2){
												temp4 = i + j;
												if (IMPages[temp4]==1){
													j = temp3;
												}else{
													j = j + 1;
												}
											}
											if (j != temp3){
												temp3 = i;
												i = QtdPagIM;
											}else{
												temp3 = 0;
												i = i + 1;
											}
										}else{
											temp3 = 0;
											i = i + 1;
										}
									}
									if(temp3 == 0){
										/*solta erro de que não há espaço livre para rodar o processo - 4*/
										temp11 = ProcessList[ActualProcess];
											
										temp2 = ProcessMemPos[temp11];
										temp2 = temp2*SizePagRAM;
										temp2 = temp2 + 1;
										temp2 = temp2+128;
										temp2 = temp2+128;
										temp2 = temp2 + 1;
										temp2 = temp2 + 1;
										/* Solta o erro de que não existe processo com o nome*/
										temp2 = temp2 + value2SysCall;
										temp1 = 65522;/*STORE_DIRECTLY 4 temp2 (salva o input direto no registrador do contexto em questão)*/
										
										temp4 = ProcessLasPC[temp11];
										temp4 = temp4 + 1;
										ProcessLasPC[temp11] = temp4;
										
										temp13 = ActualProcess + 1;
										if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
											ActualProcess = temp13;
										}else{
											ActualProcess = 0;
										}
										
										temp11 = ProcessList[ActualProcess];
																
										/*Carrega as pilhas*/
										temp2 = ProcessMemPos[temp11];
										temp2 = temp2*SizePagRAM;
										temp2 = temp2 + 1;
										temp3 = temp2+128;
										i = 0;
										while(temp2<temp3){
											temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
											temp2 = temp2 + 1;
											i = i+1;
										}
										temp3 = temp2+128;
										i = 0;
										while(temp2<temp3){
											temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
											temp2 = temp2 + 1;
											i = i+1;
										}
										temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
										temp2 = temp2 + 1;
										temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
										temp2 = temp2 + 1;
										temp2 = temp2 + 7;
										
										temp4 = ProcessLasPC[temp11];
										temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
										
										temp2 = temp2 + 1;
										temp2 = temp2 + 32;
										
										temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
										
										temp2 = ProcessLimitPC[temp11];
										temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
										
										temp2 = ProcessMemPos[temp11];
										temp2 = temp2 + 1;
										temp2 = temp2*SizePagRAM;
										temp2 = temp2 - 1;
										temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
										i = 1;if(i==0){i = 1;}
										
										temp1 = InterruptVector;
										temp1 = 65506;/*SAVE_INT temp1*/
										temp1 = 65513;/*MEM_TO_REG*/
										temp1 = 65512; /*JMP_REGISTER $7*/
									}else{
										i = SizeMemSO;
										while(i<QtdPagRAM){
											if (RAMPages[i]==0){
												temp6 = i;
												RAMPages[i] = 1;
												i = QtdPagRAM;
											}else{
												temp6 = 0;
												i = i + 1;
											}
										}
										if (temp6 == 0){
											/*solta erro de que não há espaço livre na memória para rodar o processo - 6*/
											temp11 = ProcessList[ActualProcess];
											
											temp2 = ProcessMemPos[temp11];
											temp2 = temp2*SizePagRAM;
											temp2 = temp2 + 1;
											temp2 = temp2+128;
											temp2 = temp2+128;
											temp2 = temp2 + 1;
											temp2 = temp2 + 1;
											/* Solta o erro de que não existe processo com o nome*/
											temp2 = temp2 + value2SysCall;
											temp1 = 65522;/*STORE_DIRECTLY 6 temp2 (salva o input direto no registrador do contexto em questão)*/
											
											temp4 = ProcessLasPC[temp11];
											temp4 = temp4 + 1;
											ProcessLasPC[temp11] = temp4;
											
											temp13 = ActualProcess + 1;
											if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
												ActualProcess = temp13;
											}else{
												ActualProcess = 0;
											}
											
											temp11 = ProcessList[ActualProcess];
																	
											/*Carrega as pilhas*/
											temp2 = ProcessMemPos[temp11];
											temp2 = temp2*SizePagRAM;
											temp2 = temp2 + 1;
											temp3 = temp2+128;
											i = 0;
											while(temp2<temp3){
												temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
												temp2 = temp2 + 1;
												i = i+1;
											}
											temp3 = temp2+128;
											i = 0;
											while(temp2<temp3){
												temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
												temp2 = temp2 + 1;
												i = i+1;
											}
											temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
											temp2 = temp2 + 1;
											temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
											temp2 = temp2 + 1;
											temp2 = temp2 + 7;
											
											temp4 = ProcessLasPC[temp11];
											temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
											
											temp2 = temp2 + 1;
											temp2 = temp2 + 32;
											
											temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
											
											temp2 = ProcessLimitPC[temp11];
											temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
											
											temp2 = ProcessMemPos[temp11];
											temp2 = temp2 + 1;
											temp2 = temp2*SizePagRAM;
											temp2 = temp2 - 1;
											temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
											i = 1;if(i==0){i = 1;}
											
											temp1 = InterruptVector;
											temp1 = 65506;/*SAVE_INT temp1*/
											temp1 = 65513;/*MEM_TO_REG*/
											temp1 = 65512; /*JMP_REGISTER $7*/

										}else{
											i = 0;
											while(i<temp2){
												temp4 = temp3+i;
												IMPages[temp4] = 1;
												i = i+1;
											}
											ProcessList[EndList] = temp5;
											EndList = EndList+1;
											Process[temp5] = 1;
											ProcessUID[temp5] = 0;
											ProcessDate[temp5] = 0;
											ProcessHora[temp5] = 0;
											ProcessPriority[temp5] = 2;
											ProcessInitialPos[temp5] = temp3;
											ProcessLasPC[temp5] = 0;
											ProcessSize[temp5] = FATSize[temp1];
											ProcessMemPos[temp5] = temp6;
											ProcessFATLocation[temp5] = temp1;
											Nome[temp5] = FATNome[temp1];
											temp2 = FATSize[temp1];
											temp4 = temp3*SizePagIM;
											temp4 = temp4 + temp2;
											ProcessLimitPC[temp5] = temp4;
											temp4 = FATCluster[temp1];
											temp3 = temp3*SizePagIM;
											temp4 = 65528;/*HD_LOAD_IM(temp4, temp2, temp3)//HD_LOAD(cluster inicial, quantidade em posições de memoria, posição de memoria);*/
											FATLoaded[temp1] = 1;
											
											temp2 = ProcessMemPos[temp5];
											temp2 = temp2*SizePagRAM;
											i = 0;
											temp3 = 65522;/*STORE_DIRECTLY i temp2 (last pc = 0)*/
											temp2 = temp2 + 1;
											temp3 = temp2+128;
											
											temp1 = ProcessInitialPos[temp5];
											temp1 = temp1*SizePagIM;
											temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (stack[0] = 0)*/
											temp2 = temp2 + 1;
											while(temp2<temp3){
												temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack = 0)*/
												temp2 = temp2 + 1;
											}
											temp3 = temp2+128;
											
											temp1 = ProcessMemPos[temp5];
											temp1 = temp1*SizePagRAM;
											temp1 = temp1+299;
											temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (stack[0] = 0)*/
											temp2 = temp2 + 1;
											while(temp2<temp3){
												temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack = 0)*/
												temp2 = temp2 + 1;
											}
											temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack_ptr = 0)*/
											temp2 = temp2 + 1;
											temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack_ptr = 0)*/
											temp2 = temp2 + 1;
											temp3 = temp2 + 40;
											while(temp2<temp3){
												temp1 = 65522;/*STORE_DIRECTLY i temp2 (register_bank = 0)*/
												temp2 = temp2 + 1;
											}
											
											/*------------*/
											temp11 = ProcessList[ActualProcess];
											
											temp2 = ProcessMemPos[temp11];
											temp2 = temp2*SizePagRAM;
											temp2 = temp2 + 1;
											temp2 = temp2+128;
											temp2 = temp2+128;
											temp2 = temp2 + 1;
											temp2 = temp2 + 1;
											/*salvar o input do processo falando que deu certo a chamada de sistema*/
											temp2 = temp2 + value2SysCall;
											temp1 = 65522;/*STORE_DIRECTLY 0 temp2 (salva o input direto no registrador do contexto em questão)*/
											
											/*rodar o próximo processo*/
											
											temp4 = ProcessLasPC[temp11];
											temp4 = temp4 + 1;
											ProcessLasPC[temp11] = temp4;
											
											temp13 = ActualProcess + 1;
											if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
												ActualProcess = temp13;
											}else{
												ActualProcess = 0;
											}
											
											temp11 = ProcessList[ActualProcess];
											
											/*Carrega as pilhas*/
											temp2 = ProcessMemPos[temp11];
											temp2 = temp2*SizePagRAM;
											temp2 = temp2 + 1;
											temp3 = temp2+128;
											i = 0;
											while(temp2<temp3){
												temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
												temp2 = temp2 + 1;
												i = i+1;
											}
											temp3 = temp2+128;
											i = 0;
											while(temp2<temp3){
												temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
												temp2 = temp2 + 1;
												i = i+1;
											}
											temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
											temp2 = temp2 + 1;
											temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
											temp2 = temp2 + 1;
											temp2 = temp2 + 7;
											
											temp4 = ProcessLasPC[temp11];
											temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
											
											temp2 = temp2 + 1;
											temp2 = temp2 + 32;
											
											temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
											
											temp2 = ProcessLimitPC[temp11];
											temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
											
											temp2 = ProcessMemPos[temp11];
											temp2 = temp2 + 1;
											temp2 = temp2*SizePagRAM;
											temp2 = temp2 - 1;
											temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
											i = 1;if(i==0){i = 1;}
											
											temp1 = InterruptVector;
											temp1 = 65506;/*SAVE_INT temp1*/
											temp1 = 65513;/*MEM_TO_REG*/
											temp1 = 65512; /*JMP_REGISTER $7*/
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}else{
		if (InterruptVector>=8){
			InterruptVector = InterruptVector - 8;
			
			temp5 = ProcessList[ActualProcess];
			temp1 = ProcessFATLocation[temp5];
			
			temp2 = ProcessSize[temp5];
			temp2 = temp2/SizePagIM;
			temp2 = temp2 + 1;
			
			temp3 = ProcessInitialPos[temp5];
			
			temp4 = temp3 + temp2;
			while(temp3<temp4){
				IMPages[temp3] = 0;
				temp3 = temp3 + 1;
			}
			
			ProcessInitialPos[temp5] = 0;
			
			temp3 = ProcessMemPos[temp5];
			RAMPages[temp3] = 0;
			
			ProcessMemPos[temp5] = 0;
			
			Process[temp5] = 0;
			
			EndList = EndList - 1;
			temp8 = temp11;
			while(temp11<EndList){
				temp10 = temp11 + 1;
				temp9 = ProcessList[temp10];
				ProcessList[temp11] = temp9;
				temp11 = temp10;
			}
			FATLoaded[temp1] = 0;
			
			/*salva no bash a variavel que indica que o porcesso terminou*/
			temp11 = ProcessMemPos[0];
			temp11 = temp11*SizePagRAM;
			temp11 = temp11 + 299;
			temp11 = temp11 + 3;
			temp1 = 1;
			temp1 = 65522;/*STORE_DIRECTLY temp1 temp11 (process_finished)*/
			/*termina*/
			
			if (ActualProcess > temp8){
				ActualProcess = ActualProcess - 1;
			}else{
				if (ActualProcess < temp8){
					ActualProcess = ActualProcess + 1;
				}else{
					ActualProcess = ActualProcess;
				}
			}
			
			
			temp11 = ProcessList[ActualProcess];
			
			/*Carrega as pilhas*/
			temp2 = ProcessMemPos[temp11];
			temp2 = temp2*SizePagRAM;
			temp2 = temp2 + 1;
			temp3 = temp2+128;
			i = 0;
			while(temp2<temp3){
				temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
				temp2 = temp2 + 1;
				i = i+1;
			}
			temp3 = temp2+128;
			i = 0;
			while(temp2<temp3){
				temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
				temp2 = temp2 + 1;
				i = i+1;
			}
			temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
			temp2 = temp2 + 1;
			temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
			temp2 = temp2 + 1;
			temp2 = temp2 + 7;
			
			temp4 = ProcessLasPC[temp11];
			temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
			
			temp2 = temp2 + 1;
			temp2 = temp2 + 32;
			
			temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
			
			temp2 = ProcessLimitPC[temp11];
			temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
			
			temp2 = ProcessMemPos[temp11];
			temp2 = temp2 + 1;
			temp2 = temp2*SizePagRAM;
			temp2 = temp2 - 1;
			temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
			i = 1;if(i==0){i = 1;}
			
			temp1 = InterruptVector;
			temp1 = 65506;/*SAVE_INT temp1*/
			temp1 = 65513;/*MEM_TO_REG*/
			temp1 = 65512; /*JMP_REGISTER $7*/
			
		}else{
			if (InterruptVector>=4){
				InterruptVector = InterruptVector - 4;
				

				temp5 = ProcessList[ActualProcess];
				temp1 = ProcessFATLocation[temp5];
				
				temp2 = ProcessSize[temp5];
				temp2 = temp2/SizePagIM;
				temp2 = temp2 + 1;
				
				temp3 = ProcessInitialPos[temp5];
				
				temp4 = temp3 + temp2;
				while(temp3<temp4){
					IMPages[temp3] = 0;
					temp3 = temp3 + 1;
				}
				
				ProcessInitialPos[temp5] = 0;
				
				temp3 = ProcessMemPos[temp5];
				RAMPages[temp3] = 0;
				
				ProcessMemPos[temp5] = 0;
				
				Process[temp5] = 0;
				
				EndList = EndList - 1;
				temp8 = temp11;
				while(temp11<EndList){
					temp10 = temp11 + 1;
					temp9 = ProcessList[temp10];
					ProcessList[temp11] = temp9;
					temp11 = temp10;
				}
				FATLoaded[temp1] = 0;
				
				/*salva no bash a variavel que indica que o porcesso terminou*/
				temp11 = ProcessMemPos[0];
				temp11 = temp11*SizePagRAM;
				temp11 = temp11 + 299;
				temp11 = temp11 + 3;
				temp1 = 1;
				temp1 = 65522;/*STORE_DIRECTLY temp1 temp11 (process_finished)*/
				/*termina*/
				
				if (ActualProcess > temp8){
					ActualProcess = ActualProcess - 1;
				}else{
					if (ActualProcess < temp8){
						ActualProcess = ActualProcess + 1;
					}else{
						ActualProcess = ActualProcess;
					}
				}
				
				
				temp11 = ProcessList[ActualProcess];
				
				/*Carrega as pilhas*/
				temp2 = ProcessMemPos[temp11];
				temp2 = temp2*SizePagRAM;
				temp2 = temp2 + 1;
				temp3 = temp2+128;
				i = 0;
				while(temp2<temp3){
					temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
					temp2 = temp2 + 1;
					i = i+1;
				}
				temp3 = temp2+128;
				i = 0;
				while(temp2<temp3){
					temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
					temp2 = temp2 + 1;
					i = i+1;
				}
				temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
				temp2 = temp2 + 1;
				temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
				temp2 = temp2 + 1;
				temp2 = temp2 + 7;
				
				temp4 = ProcessLasPC[temp11];
				temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
				
				temp2 = temp2 + 1;
				temp2 = temp2 + 32;
				
				temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
				
				temp2 = ProcessLimitPC[temp11];
				temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
				
				temp2 = ProcessMemPos[temp11];
				temp2 = temp2 + 1;
				temp2 = temp2*SizePagRAM;
				temp2 = temp2 - 1;
				temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
				i = 1;if(i==0){i = 1;}
				
				temp1 = InterruptVector;
				temp1 = 65506;/*SAVE_INT temp1*/
				temp1 = 65513;/*MEM_TO_REG*/
				temp1 = 65512; /*JMP_REGISTER $7*/
				
			}else{
				if (InterruptVector>=2){
					InterruptVector = InterruptVector - 2;
					
					temp13 = ActualProcess + 1;
					if(temp13<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
						ActualProcess = temp13;
					}else{
						ActualProcess = 0;
					}
					
					temp11 = ProcessList[ActualProcess];
					
					/*Carrega as pilhas*/
					temp2 = ProcessMemPos[temp11];
					temp2 = temp2*SizePagRAM;
					temp2 = temp2 + 1;
					temp3 = temp2+128;
					i = 0;
					while(temp2<temp3){
						temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
						temp2 = temp2 + 1;
						i = i+1;
					}
					temp3 = temp2+128;
					i = 0;
					while(temp2<temp3){
						temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
						temp2 = temp2 + 1;
						i = i+1;
					}
					temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
					temp2 = temp2 + 1;
					temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
					temp2 = temp2 + 1;
					temp2 = temp2 + 7;
					
					temp4 = ProcessLasPC[temp11];
					temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
					
					temp2 = temp2 + 1;
					temp2 = temp2 + 32;
					
					temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
					
					temp2 = ProcessLimitPC[temp11];
					temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
					
					temp2 = ProcessMemPos[temp11];
					temp2 = temp2 + 1;
					temp2 = temp2*SizePagRAM;
					temp2 = temp2 - 1;
					temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
					i = 1;if(i==0){i = 1;}/*salva todos os registradores na memoria do SO*/
					
					temp1 = InterruptVector;
					temp1 = 65506;/*SAVE_INT temp1*/
					temp1 = 65513;/*MEM_TO_REG*/
					temp1 = 65512; /*JMP_REGISTER $7*/
					
				}else{
					if (InterruptVector==1){
						InterruptVector = InterruptVector - 1;
						
						temp1 = 65504;/*GET_COM temp1*/
						ComPort = temp1;
						temp7 = ComPort;
						temp13 = oldComPort;
						temp12 = 0;
						temp10 = 0;
						while(temp12<4){
							if (temp7 >= 8){
								temp7 = temp7 - 8;
								if (temp13 >= 8){
									temp13 = temp13 - 8;
									temp9 = 4;
								}else{
									temp9 = 3;
								}
							}else{
								if (temp13 >= 8){
									temp13 = temp13 - 8;
									temp9 = 5;
									temp10 = 3;
								}else{
									if (temp7 >= 4){
										temp7 = temp7 - 4;
										if (temp13 >= 4){
											temp13 = temp13 - 4;
											temp9 = 4;
										}else{
											temp9 = 2;
										}
									}else{
										if (temp13 >= 4){
											temp13 = temp13 - 4;
											temp9 = 5;
											temp10 = 2;
										}else{
											if (temp7 >= 2){
												temp7 = temp7 - 2;
												if (temp13 >= 2){
													temp13 = temp13 - 2;
													temp9 = 4;
												}else{
													temp9 = 1;
												}
											}else{
												if (temp13 >= 2){
													temp13 = temp13 - 2;
													temp9 = 5;
													temp10 = 1;
												}else{
													if (temp7 >= 1){
														temp7 = temp7 - 1;
														if (temp13 >= 1){
															temp13 = temp13 - 1;
															temp9 = 4;
														}else{
															temp9 = 0;
														}
													}else{
														if (temp13 >= 1){
															temp13 = temp13 - 1;
															temp9 = 5;
															temp10 = 0;
														}else{
															temp9 = 4;
														}
													}
												}
											}
										}
									}
								}
							}
							
							if (temp9 != 4){
								if (temp9<4){
									/*Search for driver*/
									
									temp1 = 65505; /*GET_COM_N temp9 temp1;*/
									temp9 = temp9;
									COMNome[temp9] = temp1;
									temp1 = 65503; /*GET_COM_TYPE temp9 temp1;*/
									temp9 = temp9;
									COMType[temp9] = temp1;
									
									i = 0;
									while (i<300){
										if (FATNome[i] == COMNome[temp9]){
											temp1 = i;
											i = 300;
										}else{
											temp1 = 301;
											i = i +1;
										}
									}
									
									if (temp1 == 301){
										/*retorna erro de que não foi encontrado arquivo com o nome*/
										COMNome[temp9] = 0;
										COMType[temp9] = 0;
									}else{
										if (FATType[temp1] == 1){
											/*retorna erro de que não existe um processo com o mesmo nome*/
											COMNome[temp9] = 0;
											COMType[temp9] = 0;
										}else{
											i = 0;
											while(i<50){
												if(Process[i] == 0){
													temp5 = i;
													i = 50;
												}else{
													temp5 = 51;
													i = i + 1;
												}
											}
											if (temp5 == 51){
												/*retorna erro de que não pode-se executar processos ainda*/
												COMNome[temp9] = 0;
												COMType[temp9] = 0;
											}else{
												temp2 = FATSize[temp1];
												temp2 = temp2/SizePagIM;
												temp2 = temp2 + 1;
												
												i = SizeIMSO;
												while(i<QtdPagIM){
													if (IMPages[i]==0){
														j = 0;
														temp3 = temp2 + 1;
														while (j<temp2){
															temp4 = i + j;
															if (IMPages[temp4]==1){
																j = temp3;
															}else{
																j = j + 1;
															}
														}
														if (j != temp3){
															temp3 = i;
															i = QtdPagIM;
														}else{
															temp3 = 0;
															i = i + 1;
														}
													}else{
														temp3 = 0;
														i = i + 1;
													}
												}
												if(temp3 == 0){
													/*solta erro de que não há espaço livre para rodar o processo*/
													COMNome[temp9] = 0;
													COMType[temp9] = 0;
												}else{
													i = SizeMemSO;
													while(i<QtdPagRAM){
														if (RAMPages[i]==0){
															temp6 = i;
															RAMPages[i] = 1;
															i = QtdPagRAM;
														}else{
															temp6 = 0;
															i = i + 1;
														}
													}
													if (temp6 == 0){
														/*solta erro de que não há espaço livre na memória para rodar o processo*/
														COMNome[temp9] = 0;
														COMType[temp9] = 0;
													}else{
														i = 0;
														while(i<temp2){
															temp4 = temp3+i;
															IMPages[temp4] = 1;
															i = i+1;
														}
														ProcessList[EndList] = temp5;
														EndList = EndList+1;
														Process[temp5] = 1;
														ProcessUID[temp5] = 0;
														ProcessDate[temp5] = 0;
														ProcessHora[temp5] = 0;
														ProcessPriority[temp5] = 2;
														ProcessInitialPos[temp5] = temp3;
														ProcessLasPC[temp5] = 0;
														ProcessSize[temp5] = FATSize[temp1];
														ProcessMemPos[temp5] = temp6;
														ProcessFATLocation[temp5] = temp1;
														Nome[temp5] = FATNome[temp1];
														temp2 = FATSize[temp1];
														temp4 = temp3*SizePagIM;
														temp4 = temp4 + temp2;
														ProcessLimitPC[temp5] = temp4;
														temp4 = FATCluster[temp1];
														temp3 = temp3*SizePagIM;
														temp4 = 65528;/*HD_LOAD_IM(temp4, temp2, temp3)//HD_LOAD(cluster inicial, quantidade em posições de memoria, posição de memoria);*/
														FATLoaded[temp1] = 1;
														Driver[temp9] = temp5;
														
														temp2 = ProcessMemPos[temp5];
														temp2 = temp2*SizePagRAM;
														i = 0;
														temp3 = 65522;/*STORE_DIRECTLY i temp2 (last pc = 0)*/
														temp2 = temp2 + 1;
														temp3 = temp2+128;
														
														temp1 = ProcessInitialPos[temp5];
														temp1 = temp1*SizePagIM;
														temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (stack[0] = 0)*/
														temp2 = temp2 + 1;
														while(temp2<temp3){
															temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack = 0)*/
															temp2 = temp2 + 1;
														}
														temp3 = temp2+128;
														
														temp1 = ProcessMemPos[temp5];
														temp1 = temp1*SizePagRAM;
														temp1 = temp1+299;
														temp1 = 65522;/*STORE_DIRECTLY temp1 temp2 (stack[0] = 0)*/
														temp2 = temp2 + 1;
														while(temp2<temp3){
															temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack = 0)*/
															temp2 = temp2 + 1;
														}
														temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack_ptr = 0)*/
														temp2 = temp2 + 1;
														temp1 = 65522;/*STORE_DIRECTLY i temp2 (stack_ptr = 0)*/
														temp2 = temp2 + 1;
														temp3 = temp2 + 40;
														while(temp2<temp3){
															temp1 = 65522;/*STORE_DIRECTLY i temp2 (register_bank = 0)*/
															temp2 = temp2 + 1;
														}
														temp9 = temp9;
														temp1 = 65522;/*STORE_DIRECTLY temp9 temp2 (Comport = temp9)*/
													}
												}
											}
										}
									}
									
									/*------------*/
									temp11 = ProcessList[ActualProcess];
									
									temp2 = ProcessMemPos[temp11];
									temp2 = temp2*SizePagRAM;
									temp2 = temp2 + 1;
									temp2 = temp2+128;
									temp2 = temp2+128;
									temp2 = temp2 + 1;
									temp2 = temp2 + 1;
																		
									/*rodar o próximo processo*/
									
									
									temp4 = ActualProcess + 1;
									if(temp4<EndList){/*o ActualProcess nunca vai ser igual o EndList*/
										ActualProcess = temp4;
									}else{
										ActualProcess = 0;
									}
									temp11 = ProcessList[ActualProcess];
									
									/*Carrega as pilhas*/
									temp2 = ProcessMemPos[temp11];
									temp2 = temp2*SizePagRAM;
									temp2 = temp2 + 1;
									temp3 = temp2+128;
									i = 0;
									while(temp2<temp3){
										temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
										temp2 = temp2 + 1;
										i = i+1;
									}
									temp3 = temp2+128;
									i = 0;
									while(temp2<temp3){
										temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
										temp2 = temp2 + 1;
										i = i+1;
									}
									temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
									temp2 = temp2 + 1;
									temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
									temp2 = temp2 + 1;
									temp2 = temp2 + 7;
									
									temp4 = ProcessLasPC[temp11];
									temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
									
									temp2 = temp2 + 1;
									temp2 = temp2 + 32;
									
									temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
									
									temp2 = ProcessLimitPC[temp11];
									temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
									
									temp2 = ProcessMemPos[temp11];
									temp2 = temp2 + 1;
									temp2 = temp2*SizePagRAM;
									temp2 = temp2 - 1;
									temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
									i = 1;if(i==0){i = 1;}
									
									temp1 = InterruptVector;
									temp1 = 65506;/*SAVE_INT temp1*/
									temp1 = 65513;/*MEM_TO_REG*/
									temp1 = 65512; /*JMP_REGISTER $7*/
								}else{
									if (temp10 == 0){
										pointerBuffer1 = 0;
										endPointerBuffer1 = 0;
									}else{
										if (temp10 == 1){
											pointerBuffer2 = 0;
											endPointerBuffer2 = 0;
										}else{
											if (temp10 == 2){
												pointerBuffer3 = 0;
												endPointerBuffer3 = 0;
											}else{
												if(temp10 == 3){
													pointerBuffer4 = 0;
													endPointerBuffer4 = 0;
												}
											}
										}
									}
													
									temp11 = 51;
									i = 0;
									temp8 = Driver[temp10];
									Driver[temp10] = 0;
									COMNome[temp10] = 0;
									COMType[temp10] = 0;
									
									while (i < EndList){
										temp9 = ProcessList[i];
										if (temp8 == temp9){
											temp11 = i;
											i = EndList;
										}else{
											i = i + 1;
										}
									}
									
									if(temp11!=51){
										temp5 = ProcessList[temp11];
										temp1 = ProcessFATLocation[temp5];
										
										temp2 = ProcessSize[temp5];
										temp2 = temp2/SizePagIM;
										temp2 = temp2 + 1;
										
										temp3 = ProcessInitialPos[temp5];
										
										temp4 = temp3 + temp2;
										while(temp3<temp4){
											IMPages[temp3] = 0;
											temp3 = temp3 + 1;
										}
										
										ProcessInitialPos[temp5] = 0;
										
										temp3 = ProcessMemPos[temp5];
										RAMPages[temp3] = 0;
										
										ProcessMemPos[temp5] = 0;
										
										Process[temp5] = 0;
										
										EndList = EndList - 1;
										temp8 = temp11;
										while(temp11<EndList){
											temp10 = temp11 + 1;
											temp9 = ProcessList[temp10];
											ProcessList[temp11] = temp9;
											temp11 = temp10;
										}
										FATLoaded[temp1] = 0;
										
										if (ActualProcess > temp8){
											ActualProcess = ActualProcess - 1;
										}else{
											if (ActualProcess < temp8){
												ActualProcess = ActualProcess + 1;
											}else{
												ActualProcess = ActualProcess;
											}
										}
										
										
										temp11 = ProcessList[ActualProcess];
										
										/*Carrega as pilhas*/
										temp2 = ProcessMemPos[temp11];
										temp2 = temp2*SizePagRAM;
										temp2 = temp2 + 1;
										temp3 = temp2+128;
										i = 0;
										while(temp2<temp3){
											temp1 = 65520;/*LOAD_STACK_R 0 temp2 i*/
											temp2 = temp2 + 1;
											i = i+1;
										}
										temp3 = temp2+128;
										i = 0;
										while(temp2<temp3){
											temp1 = 65519;/*LOAD_STACK_PC 0 temp2 i*/
											temp2 = temp2 + 1;
											i = i+1;
										}
										temp1 = 65518;/*LOAD_PTR_R 0 temp2*/
										temp2 = temp2 + 1;
										temp1 = 65517;/*LOAD_PTR_PC 0 temp2*/
										temp2 = temp2 + 1;
										temp2 = temp2 + 7;
										
										temp4 = ProcessLasPC[temp11];
										temp1 = 65522;/*STORE_DIRECTLY temp4 temp2 (GRAVA O last_PC no $7*/
										
										temp2 = temp2 + 1;
										temp2 = temp2 + 32;
										
										temp1 = 65511; /*SET_MEM_BEG 0 temp2*/
										
										temp2 = ProcessLimitPC[temp11];
										temp1 = 65530;/*SET_LIMIT_PC 0 temp2*/
										
										temp2 = ProcessMemPos[temp11];
										temp2 = temp2 + 1;
										temp2 = temp2*SizePagRAM;
										temp2 = temp2 - 1;
										temp1 = 65529;/*SET_LIMIT_MEM 0 temp2*/
										i = 1;if(i==0){i = 1;}
										
										temp1 = InterruptVector;
										temp1 = 65506;/*SAVE_INT temp1*/
										temp1 = 65513;/*MEM_TO_REG*/
										temp1 = 65512; /*JMP_REGISTER $7*/
									}
								}
							}
							temp12 = temp12 + 1;
						}
					}
				}
			}
		}
	}
}