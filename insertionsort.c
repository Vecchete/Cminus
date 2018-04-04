int vetor[3];
int sort(int j){
	int i;
	int chave;
	int retorno;
	int flagexit;
	int deslocamento;
	flagexit = 0;
	i = j;
	if (j>=3){
		return 0;
	}else{
		chave = vetor[j];
		if (i == 0){
			vetor[i] = chave;
			j = j + 1;
			retorno = sort(j);
			return retorno;
		}else{
			while(flagexit != 1){
				if (i == 0){
					flagexit = 1;
				}else{
					deslocamento = i-1;
					if (vetor[deslocamento] > chave){
						vetor[i] = vetor[deslocamento];
						i = i - 1;
					}else{
						flagexit = 1;
					}
				}
			}
			vetor[i] = chave;
			j = j + 1;
			retorno = sort(j);
			return retorno;
		}
	}
}
void main(void){
  int saida;
  int contador;
  int cont;
  int a;
  a = 3;
  cont = 0;
  while(cont < 3){
	vetor[cont] = a;
	cont = cont + 1;
	a = a - 1;
  }
  contador = 1;
  saida = sort(contador);
}