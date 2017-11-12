#include <fstream>
#include <iostream>
#include <queue>
#include <vector>
#include <tuple>
#include <algorithm>
#include <unordered_set>
#include <unordered_map>
using namespace std;
namespace works {
	struct DKA
	{
		unsigned int n;// количество состояний
		unsigned int m;// переходов
		unsigned int k; //допускающих состояний
		vector<int> num_k; //допускающие состояния
		vector<tuple<int, int, char>> transitions;
	};
	namespace Isomorphism {
		void start(ifstream& file);
		int** make_table(DKA& machine) {
			vector<int> gray;
			vector<int> black;
			vector<int> memory;
			memory.push_back(std::get<0>(machine.transitions[0]));
			gray.push_back(memory.back());
			while (memory.size() != 0)
			{
				bool find_transition = false;
				for (int i = 0; i < machine.transitions.size(); i++)
				{
					bool findinblack = false;
					for (int j = 0; j < black.size(); j++)
					{
						if (std::get<1>(machine.transitions[i]) == black[j])
						{
							findinblack = true;
						}
					}
					if (memory.back() == std::get<0>(machine.transitions[i]) && findinblack == false)
					{
						find_transition = true;

						bool graylist = false;
						for (int k = 0; k < gray.size(); k++)
						{
							if (std::get<1>(machine.transitions[i]) == gray[k])
							{
								graylist = true;
								break;
							}
						}
						if (graylist == false)
						{
							memory.push_back(std::get<1>(machine.transitions[i]));
							gray.push_back(std::get<1>(machine.transitions[i]));
						}
						else
						{
							//memory.push_back(std::get<1>(machine.transitions[i]));
							black.push_back(memory.back());
							memory.pop_back();
						}
					}

					if (find_transition == false && i == machine.transitions.size() - 1)
					{
						black.push_back(memory.back());
						memory.pop_back();
					}
				}
			}
			for (int j = 0; j < machine.transitions.size(); j++)
			{
				bool find = false;
				for (int i = 0; i < black.size(); i++)
				{
					if (get<0>(machine.transitions[j]) == black[i])
					{
						find = true;
					}
				}
				if (find == false)
				{
					machine.transitions.erase(machine.transitions.begin() + j);
				}
			}
			int c = 0;
			int** table = new int*[machine.n];
			for (int i = 0; i < machine.n; i++)
			{
				table[i] = new int[machine.n];
			}
			for (int i = 0, find_end = 0; i < machine.n; i++)
			{
				for (int j = 0; j < machine.n; j++)
				{
					for (int k = 0, find_eq = 0; k < machine.num_k.size(); k++)
					{
						for (int z = 0; z < machine.num_k.size(); z++)
						{
							if (j == machine.num_k[k] - 1 && i == machine.num_k[z] - 1 && z != k)
							{
								find_eq = 1;
							}
							else if (i == machine.num_k[k] - 1 && j == machine.num_k[z] - 1 && z != k)
							{
								find_eq = 1;
							}
						}
						if (i == machine.num_k[k] - 1 && find_eq == 0)
						{
							table[i][j] = 1;
						}
						if (j == machine.num_k[k] - 1 && find_eq == 0)
						{
							table[i][j] = 1;
						}
					}
					if (i == j)
					{
						table[i][j] = 2;
					}
					if (table[i][j] != 1 && table[i][j] != 2)
					{
						table[i][j] = 0;
					}
				}
			}
			for (int i = 0; i < machine.n; i++)
			{
				for (int j = 0; j < machine.n; j++)
				{
					printf("%i ", table[i][j]);
				}
				printf("\n");
			}
			return table;
		};
		bool match(int N, int** A, int** B, std::vector<int> P);
	}
	namespace equivalence {
		void start(ifstream& file);
		bool dfs(int** A, int** B, vector<int> terminal_1, vector<int> terminal_2, int size_table_first, int size_table_second, std::vector<int> size_symbol_first_table, std::vector<int> size_symbol_second_table);
	}
	namespace Minimization {
		bool** make_table(DKA& machine) {
			struct data {
				int first, second;
			};
			std::queue<data> Q;
			std::vector<std::vector<std::vector<int>>>  table_list;
			table_list.resize(machine.n);
			int max_symbol = 0;
			for (auto k_iter = machine.transitions.begin(); k_iter != machine.transitions.end(); k_iter++)
			{
				if (max_symbol < std::get<2>(*k_iter))
					max_symbol = std::get<2>(*k_iter);
			}
			max_symbol -= 96;
			for (auto i = table_list.begin(); i != table_list.end(); i++)
				(*i).resize(max_symbol);
			for (int i = 0, find_end = 0; i < machine.n; i++)
			{
				for (int j = 0; j < max_symbol; j++)
				{
					for (auto k_iter = machine.transitions.begin(); k_iter != machine.transitions.end(); k_iter++)
					{
						if (i + 1 == std::get<1>(*k_iter) && j + 97 == std::get<2>(*k_iter))
							table_list[i][j].push_back(std::get<0>(*k_iter) - 1);
					}
				}
			}
			/*		for (auto i = table_list.begin(); i != table_list.end(); i++)
					{
						for (auto j = (*i).begin(); j != (*i).end(); j++)
						{
							for (auto k = (*j).begin();k!= (*j).end(); k++)
								printf("%i ", (*k));
							printf("\n");
						}
						printf("\n");
					}*/
			bool** marked = new bool*[machine.n];
			for (int i = 0; i < machine.n; i++)
			{
				marked[i] = new bool[machine.n];
			}
			for (int i = 0, find_end = 0; i < machine.n; i++)
				for (int j = 0; j < machine.n; j++)
					marked[i][j] = false;
			for (int i = 0, find_end = 0; i < machine.n; i++)
			{
				for (int j = 0; j < machine.n; j++)
				{
					if (marked[i][j] == false)
					{
						bool find_i = false;
						for (auto k_iter = machine.num_k.begin(); k_iter != machine.num_k.end(); k_iter++)
						{
							if (*k_iter == i)
							{
								find_i = true;
								bool find_eq = false;
								for (auto k_iter = machine.num_k.begin(); k_iter != machine.num_k.end(); k_iter++)
									if (*k_iter == j)
										find_eq = true;
								if (find_eq == false)
								{
									marked[i][j] = true;
									marked[j][i] = true;
									data res;
									res.first = i;
									res.second = j;
									Q.push(res);
								}
							}
						}
						if (find_i == false)
						{
							for (auto k_iter = machine.num_k.begin(); k_iter != machine.num_k.end(); k_iter++)
								if (*k_iter == j)
								{
									marked[i][j] = true;
									marked[j][i] = true;
									data res;
									res.first = i;
									res.second = j;
									Q.push(res);
								}
						}
					}
				}
			}
			for (int i = 0; i < machine.n; i++)
			{
				for (int j = 0; j < machine.n; j++)
				{
					printf("%i ", marked[i][j]);
				}
				printf("\n");
			}
			while (!Q.empty())
			{
				data res, write;
				res.first = Q.front().first;
				res.second = Q.front().second;
				Q.pop();
				for (int u = 0; u < max_symbol; u++)
				{
					for (auto k_iter = table_list[res.first][u].begin(); k_iter != table_list[res.first][u].end(); k_iter++)
					{
						for (auto j_iter = table_list[res.second][u].begin(); j_iter != table_list[res.second][u].end(); j_iter++)
						{
							if (marked[*k_iter][*j_iter] != true)
							{
								marked[*k_iter][*j_iter] = true;
								marked[*j_iter][*k_iter] = true;
								write.first = *k_iter;
								write.second = *j_iter;
								Q.push(write);
							}
						}
					}
				}
			}

			return marked;
		}
		void start(ifstream& file);
	}
	namespace Hopcroft {
		void start(ifstream& file);
	}
}
void works::Hopcroft::start(ifstream & file)
{
	DKA machine;
	file >> machine.n;
	file >> machine.m;
	file >> machine.k;
	vector<bool> terminal(machine.n, false);
	for (int i = 0, copy; i < machine.k; i++)
	{
		file >> copy;

		terminal[copy - 1] = true;
	}
	vector<unordered_map<char, size_t > > g(machine.n);
	{
		size_t a, b;
		char c;
		for (int i = 0; i < machine.m; i++)
		{
			file >> a;
			if (file.eof())
				break;
			file >> b;
			file >> c;
			g[a - 1][c] = b - 1;
		}
	}
	////////////////////////////удаляем недостижимые состояния
		int start = 0;
	{
		queue<size_t> q;
		vector<bool> used(machine.n);
		used[start] = true;
		q.push(start);
		while (!q.empty())
		{
			size_t now = q.front();
			q.pop();
			for (char ch = 'a'; ch < 'a' + 26; ch++)
			{
				if (!g[now].count(ch))
					continue;
				size_t to = g[now][ch];
				if (!used[to])
				{
					used[to] = true;
					q.push(to);
				}
			}
		}
		for (size_t i = 0; i < machine.n; i++)
			if (!used[i])
			{
				for (char ch = 'a'; ch < 'a' + 26; ch++)
					g[i][ch] = i;
				terminal[i] = false;
			}
	}
	/////////////////////////////////////////////////////////////
	{
		g.push_back(unordered_map<char, size_t>());
		terminal.push_back(false);
		size_t hell = machine.n;
		machine.n++;
	///////////////////добавляем недостижимые состояния
		for (size_t i = 0; i < machine.n; i++)
		{
			for (char ch = 'a'; ch < 'a' + 26; ch++)
				if (!g[i].count(ch))
					g[i][ch] = hell;
		}
		for (char ch = 'a'; ch < 'a' + 26; ch++)
			g[hell][ch] = hell;
	}

	vector<size_t> eqlass(machine.n);
	vector<unordered_set<size_t> > classes(2);
	vector<bool> inQueue(2, true);
	vector<bool> brokenstate(2, true);
	///////////////////////////разбиваем на классы терминальных и нетерминальных состояний 
	for (size_t i = 0; i < machine.n; i++)
	{
		eqlass[i] = terminal[i];
		classes[eqlass[i]].insert(i);
	}
	vector<unordered_map<char, vector<size_t> > > gInv(machine.n);
	///////////////////////определяем достижимые состояния
	for (size_t i = 0; i < machine.n; i++)
		for (unordered_map<char, size_t>::const_iterator it = g[i].begin(); it != g[i].end(); it++)
			gInv[it->second][it->first].push_back(i);
	vector<size_t> q;
	if (classes[0].size() < classes[1].size())
		q.push_back(0);
	else
		q.push_back(1);

	int p1 = 0, p2 = 1; //замена пустой очереди
	while (p1 < p2)
	{
		size_t Id_classes = q[p1++];
		if (!inQueue[Id_classes])
			continue;
		inQueue[Id_classes] = false;
		unordered_set<size_t> allwaysinclass = classes[Id_classes];
		unordered_map<size_t, size_t> timesUsed;
		for (char ch = 'a'; ch < 'a' + 26; ch++)
		{
			unordered_set<size_t> domain;
			for (unordered_set<size_t>::const_iterator it = allwaysinclass.begin(); it != allwaysinclass.end(); it++)
			{
				for (vector<size_t>::const_iterator it2 = gInv[*it][ch].begin(); it2 != gInv[*it][ch].end(); it2++)
				{
					domain.insert(eqlass[*it2]);
					timesUsed[eqlass[*it2]]++;
				}
			}
			for (unordered_set<size_t>::const_iterator it2 = domain.begin(); it2 != domain.end(); it2++)
			{
				size_t splitMe = *it2;
				if (classes[splitMe].size() == timesUsed[splitMe])
					continue;
				unordered_set<size_t> r1, r2;
				for (unordered_set<size_t>::const_iterator it3 = classes[splitMe].begin(); it3 != classes[splitMe].end(); it3++)
				{
					size_t v = *it3;
					if (g[v].count(ch) && allwaysinclass.count(g[v][ch]))
						r1.insert(v);
					else
						r2.insert(v);
				}
				if (r1.size() != 0 && r2.size() != 0)
				{
					inQueue.push_back(true);
					inQueue.push_back(true);
					brokenstate.push_back(true);
					brokenstate.push_back(true);
					size_t r1ID = classes.size();
					classes.push_back(r1);
					size_t r2ID = classes.size();
					classes.push_back(r2);
					classes[splitMe].clear();
					brokenstate[splitMe] = false;
					for (unordered_set<size_t>::const_iterator it = r1.begin(); it != r1.end(); it++)
						eqlass[*it] = r1ID;
					for (unordered_set<size_t>::const_iterator it = r2.begin(); it != r2.end(); it++)
						eqlass[*it] = r2ID;
					if (inQueue[splitMe])
					{
						inQueue[splitMe] = false;
						q.push_back(r1ID);
						q.push_back(r2ID);
						p2 += 2;
					}
					else {
						if (r1.size() < r2.size())
						{
							q.push_back(r1ID);
							p2++;
						}
						else {
							q.push_back(r2ID);
							p2++;
						}
					}
				}
			}
		}
	}
	vector<size_t> newID(brokenstate.size(), -1);
	size_t vcnt = 0;
	for (size_t i = 0; i < brokenstate.size(); i++)
		if (brokenstate[i])
			newID[i] = vcnt++;/////////////////////определяем состояния нового дка
	vector<bool> newTerminal(vcnt, false);
	for (size_t i = 0; i < machine.n; i++)
		if (terminal[i])
			newTerminal[newID[eqlass[i]]] = true;//////////////создаем терминальные состояния
	vector<unordered_map<char, size_t> > newG(vcnt);
	for (size_t i = 0; i < machine.n; i++)
		for (unordered_map<char, size_t>::const_iterator it = g[i].begin(); it != g[i].end(); it++)
			newG[newID[eqlass[i]]][it->first] = newID[eqlass[it->second]];
	machine.n = vcnt;
	size_t hell = machine.n + 1;
	for (size_t i = 0; i < machine.n; i++)
	{
		bool good = false;
		for (char ch = 'a'; ch < 'a' + 26; ch++)
		{
			if (newG[i][ch] != i)
			{
				good = true;
				break;
			}
		}
		if (!good)
		{
			hell = i;
			break;
		}
	}
	//swap_id
	{
		for (size_t i = 0; i < machine.n; i++)
			for (char ch = 'a'; ch < 'a' + 26; ch++)
			{
				if (!newG[i].count(ch))
					continue;
				if (newG[i][ch] == hell)
					newG[i][ch] = machine.n - 1;
				else if (newG[i][ch] == machine.n - 1)
					newG[i][ch] = hell;
			}
		std::swap(newG[hell], newG[machine.n - 1]);
		bool tmp = newTerminal[hell];
		newTerminal[hell] = newTerminal[machine.n - 1];
		newTerminal[machine.n - 1] = tmp;
		if (start == hell)
			start = machine.n - 1;
		else if (start == machine.n - 1)
			start = hell;
	}
	newG.pop_back();
	newTerminal.pop_back();
	machine.n--;
	for (size_t i = 0; i <  machine.n; i++)
	{
		for (char ch = 'a'; ch < 'a' + 26; ch++)
		{
			if (newG[i][ch] == machine.n)
				newG[i].erase(ch);
		}
	}
	start = newID[eqlass[start]];
	hell = start;
	{
		for (size_t i = 0; i < machine.n; i++)
			for (char ch = 'a'; ch < 'a' + 26; ch++)
			{
				if (!newG[i].count(ch))
					continue;
				if (newG[i][ch] == hell)
					newG[i][ch] = 0;
				else if (newG[i][ch] == 0)
					newG[i][ch] = hell;
			}
		std::swap(newG[hell], newG[0]);
		bool tmp = newTerminal[hell];
		newTerminal[hell] = newTerminal[0];
		newTerminal[0] = tmp;
		if (start == hell)
			start = 0;
		else if (start == 0)
			start = hell;
	}
	start = 0;
	size_t m = 0;
	for (vector<unordered_map<char, size_t> >::const_iterator it = newG.begin(); it != newG.end(); it++)
		m += it->size();
	size_t k = 0;
	for (size_t i = 0; i < newTerminal.size(); i++)
		k += newTerminal[i];
	size_t n = newTerminal.size();
	cout << n << " " << m << " " << k << "\n";
	for (size_t i = 0; i < newTerminal.size(); i++)
		if (newTerminal[i])
			cout << (i + 1) << " ";
	cout << "\n";
	for (size_t i = 0; i < n; i++)
		for (unordered_map<char, size_t>::const_iterator it = newG[i].begin(); it != newG[i].end(); it++)
			cout << (i + 1) << " " << (it->second + 1) << " " << it->first << "\n";
}

bool works::Isomorphism::match(int N, int** A, int** B, std::vector<int> P) {
	for (int i = 0; i < N; i++)
		for (int j = 0; j < N; j++)
			if (A[i][j] != B[P[i]][P[j]])
				return false;
	return true;
}
void works::Isomorphism::start(ifstream& file)
{
	DKA machine;
	DKA machine_2;
	file >> machine.n;
	file >> machine.m;
	file >> machine.k;
	for (int i = 0, copy; i < machine.k; i++)
	{
		file >> copy;
		machine.num_k.push_back(copy);
	}
	{
		int a, b;
		char c;
		while (!file.eof())
		{
			file >> a;

			if (file.eof())
				break;
			file >> b;
			file >> c;
			if (c < 59)
			{
				c -= 48;
				break;
			}

			machine.transitions.push_back(make_tuple(a, b, c));
		}
		machine_2.n = a;
		machine_2.m = b;
		machine_2.k = c;
		for (int i = 0, copy; i < machine_2.k; i++)
		{
			file >> copy;
			machine_2.num_k.push_back(copy);
		}
		while (!file.eof())
		{
			file >> a;
			if (a == 0)
				break;
			if (file.eof())
				break;
			file >> b;
			file >> c;
			if (c < 59)
				break;
			machine_2.transitions.push_back(make_tuple(a, b, c));
		}
	}
	int** table_1 = make_table(machine);
	printf("\n");
	int** table_2 = make_table(machine_2);
	std::vector<int> P;
	for (int i = 0; i < machine.n; i++)
		P.emplace_back(i);
	do {
		if (match(machine.n, table_1, table_2, P)) {
			cout << true << endl;
			for (int i = 0; i < machine.n; i++)
				cout << P[i] << " ";
			break;
		}
	} while (next_permutation(P.data(), P.data() + machine.n));
}
bool works::equivalence::dfs(int** A, int** B, vector<int> terminal_1, vector<int> terminal_2, int size_table_first, int size_table_second, std::vector<int> size_symbol_first_table, std::vector<int> size_symbol_second_table)
{
	struct data {
		int first, second;
	}data_queue, data_used;
	std::queue<data> Q;
	data_queue.first = 0;
	data_queue.second = 0;
	Q.push(data_queue);
	vector<int> used_first(size_table_first, false);
	vector<int> used_second(size_table_second, false);
	while (!Q.empty())
	{
		data_queue = Q.back();
		Q.pop();
		for (auto i = terminal_1.begin(); i != terminal_1.end(); i++)
			if (data_queue.first == *i)
			{
				bool term = false;
				for (auto y = terminal_2.begin(); y != terminal_2.end(); y++)
					if (data_queue.second == *y)
						term = true;
				if (term == false)
					return false;
			}
			else {
				bool term = false;
				for (auto y = terminal_2.begin(); y != terminal_2.end(); y++)
					if (data_queue.second == *y)
						term = true;
				if (term == true)
					return false;
			}

			used_first[data_queue.first] = true;
			used_second[data_queue.second] = true;
			for (auto i = size_symbol_first_table.begin(); i < size_symbol_first_table.end(); i++)
			{
				for (auto j = size_symbol_second_table.begin(); j < size_symbol_second_table.end(); j++)
				{
					if (*i == *j)
					{
						if (used_first[A[data_queue.first][*i]] == false && used_second[B[data_queue.second][*j]] == false)
						{
							data_used.first = A[data_queue.first][*i];
							data_used.second = B[data_queue.second][*j];
							Q.push(data_used);
						}
					}
					else
						return false;
				}
			}
	}
	return true;
}
void works::equivalence::start(ifstream& file)
{
	DKA machine_1;
	DKA machine_2;
	file >> machine_1.n;
	file >> machine_1.m;
	file >> machine_1.k;
	std::vector<int> first_language;
	std::vector<int> second_language;
	int max_char_first_machine = 0, max_char_second_machine = 0;
	int max_int_first_machine_first = 0, max_int_second_machine_first = 0;
	int max_int_first_machine_second = 0, max_int_second_machine_second = 0;
	for (int i = 0, copy; i < machine_1.k; i++)
	{
		file >> copy;
		machine_1.num_k.push_back(copy - 1);
	}
	{
		int a = 0, b = 0;
		char c = 0;
		while (!file.eof())
		{
			file >> a;

			if (file.eof())
				break;
			file >> b;
			file >> c;
			if (c < 59)
			{
				c -= 48;
				break;
			}
			if (max_int_first_machine_first < a)
				max_int_first_machine_first = a;
			if (max_int_first_machine_second < b)
				max_int_first_machine_second = b;
			if (max_char_first_machine < c)
				max_char_first_machine = c;
			machine_1.transitions.push_back(make_tuple(a, b, c));
			first_language.push_back(c - 97);
		}
		machine_2.n = a;
		machine_2.m = b;
		machine_2.k = c;
		for (int i = 0, copy; i < machine_2.k; i++)
		{
			file >> copy;
			machine_2.num_k.push_back(copy - 1);
		}

		while (!file.eof())
		{
			file >> a;
			if (a == 0)
				break;
			if (file.eof())
				break;
			file >> b;
			file >> c;
			if (max_int_second_machine_first < a)
				max_int_second_machine_first = a;
			if (max_int_second_machine_second < b)
				max_int_second_machine_second = b;
			if (max_char_second_machine < c)
				max_char_second_machine = c;
			machine_2.transitions.push_back(make_tuple(a, b, c));
			second_language.push_back(c - 97);
		}
	}
	max_char_second_machine -= 96;
	max_char_first_machine -= 96;
	int max_char = std::max(max_char_first_machine, max_char_second_machine);
	max_int_first_machine_first = std::max(max_int_first_machine_first, max_int_first_machine_second);
	max_int_second_machine_first = std::max(max_int_second_machine_second, max_int_second_machine_first);

	int** table_first = new int*[max_int_first_machine_first];
	int** table_second = new int*[max_int_second_machine_first];
	for (int i = 0; i < max_int_first_machine_first; i++)
		table_first[i] = new int[max_char];
	for (int i = 0; i < max_int_second_machine_first; i++)
		table_second[i] = new int[max_char];

	for (int y = 0; y < max_int_first_machine_first; y++)
		for (int i = 0; i < max_char; i++)
		{
			table_first[y][i] = 0;
		}
	for (int y = 0; y < max_int_second_machine_first; y++)
		for (int i = 0; i < max_char; i++)
		{
			table_second[y][i] = 0;
		}
	for (auto i = machine_1.transitions.begin(); i != machine_1.transitions.end(); i++)
		table_first[std::get<0>(*i) - 1][std::get<2>(*i) - 97] = std::get<1>(*i) - 1;
	for (auto i = machine_2.transitions.begin(); i != machine_2.transitions.end(); i++)
		table_second[std::get<0>(*i) - 1][std::get<2>(*i) - 97] = std::get<1>(*i) - 1;
	/*for (int y = 0; y < max_int_first_machine_first; y++)
	{
		for (int i = 0; i < max_char; i++)
			cout << table_first[y][i];
		cout << endl;
	}
	for (int y = 0; y < max_int_second_machine_first; y++)
	{
		for (int i = 0; i < max_char; i++)
			cout << table_second[y][i];
		cout << endl;
	}*/
	std::cout << dfs(table_first, table_second, machine_1.num_k, machine_2.num_k, max_int_first_machine_second, max_int_second_machine_second, first_language, second_language);
	for (int i = 0; i < max_int_first_machine_first; i++)
		delete[] table_first[i];
	for (int i = 0; i < max_int_second_machine_first; i++)
		delete[] table_second[i];
	delete[] table_first;
	delete[] table_second;
}
void works::Minimization::start(ifstream& file)
{
	DKA machine;
	file >> machine.n;
	file >> machine.m;
	file >> machine.k;
	for (int i = 0, copy; i < machine.k; i++)
	{
		file >> copy;
		machine.num_k.push_back(copy - 1);
	}
	{
		int a, b;
		char c;
		while (!file.eof())
		{
			file >> a;

			if (a == 0)
				break;
			if (file.eof())
				break;
			file >> b;
			file >> c;
			machine.transitions.push_back(make_tuple(a, b, c));
		}
	}
	std::vector<int> reachable(machine.n);

	vector<int> states;
	vector<int> memory;
	states.push_back(std::get<0>(machine.transitions[0]));
	memory.push_back(states[0]);
	while (states.size() != 0)
	{
		for (int i = 0; i < states.size(); i++)
		{
			for (auto j = machine.transitions.begin(); j != machine.transitions.end(); j++)
			{
				if (std::get<0>(*j) == states[i])
				{
					bool find = false;
					for (auto k = memory.begin(); k != memory.end(); k++)
					{
						if (*k == std::get<1>(*j))
						{
							find = true;
						}
					}
					if (find == false)
						states.push_back(std::get<1>(*j));
				}
			}
			memory.push_back(states[i]);
			states.erase(states.begin() + i);
		}
	}
	for (auto j = memory.begin(); j != memory.end(); j++)
	{
		reachable[(*j) - 1] = 1;
	}
	bool** marked = make_table(machine);
	int* component = new int[machine.n];
	for (int i = 0; i < machine.n; i++)
		component[i] = -1;
	for (int i = 0; i < machine.n; i++)
		if (0 == marked[0][i])
			component[i] = 0;

	int componentsCount = 0;
	for (int i = 0; i < machine.n; i++)
	{
		if (reachable[i] == 0)
			continue;
		if (component[i] == -1)
		{
			componentsCount++;
			component[i] = componentsCount;
			for (int j = 0; j < machine.n; j++)
			{
				if (marked[i][j] == false)
				{
					component[j] = componentsCount;
				}
			}
		}
	}
	cout << endl << endl;
	for (int i = 0; i < machine.n; i++)
		cout << component[i];
	cout << endl << endl;
	for (int i = 0; i < machine.n; i++)
	{
		for (int y = 0; y < machine.n; y++)
			cout << marked[i][y];
		cout << endl;
	}
	std::vector<int> index;
	for (int i = 0; i < machine.n; i++)
	{
		if (component[i] != -1)
		{
			if (i > 0)
			{
				if (component[i] != component[i - 1])
					for (int j = 0; j < machine.transitions.size(); j++)
					{
						if (std::get<0>(machine.transitions[j]) == i + 1)
						{
							index.push_back(std::get<0>(machine.transitions[j]));
						}
					}
			}
			else
			{
				for (int j = 0; j < machine.transitions.size(); j++)
				{
					if (std::get<0>(machine.transitions[j]) == i + 1)
					{
						index.push_back(std::get<0>(machine.transitions[j]));
					}
				}
			}
		}
	}
	for (int j = 0; j < machine.num_k.size(); j++)
	{
		bool find = false;
		for (int i = 0; i < index.size() - 1; i++)
		{
			if (index[i] <machine.num_k[j] + 1 && index[i + 1]>machine.num_k[j] + 1)
				find = true;
		}
		if (find == false)
			cout << machine.num_k[j] + 1 << "   ";
	}

	cout << endl;
	for (int i = 0; i < machine.n; i++)
	{
		if (component[i] != -1)
		{
			if (i > 0)
			{
				if (component[i] != component[i - 1])
					for (int j = 0; j < machine.transitions.size(); j++)
					{
						if (std::get<0>(machine.transitions[j]) == i + 1)
						{
							for (int k = 0; k < index.size() - 1; k++)
							{
								if (index[k] <std::get<1>(machine.transitions[j]) && index[k + 1]>std::get<1>(machine.transitions[j]))
									std::get<1>(machine.transitions[j]) = index[k];
							}
							cout << std::get<0>(machine.transitions[j]) << "   " << std::get<1>(machine.transitions[j]) << "    " << std::get<2>(machine.transitions[j]);
							cout << endl;
						}
					}
			}
			else
			{
				for (int j = 0; j < machine.transitions.size(); j++)
				{
					if (std::get<0>(machine.transitions[j]) == i + 1)
					{
						for (int k = 0; k < index.size() - 1; k++)
						{
							if (index[k] <std::get<1>(machine.transitions[j]) && index[k + 1]>std::get<1>(machine.transitions[j]))
								std::get<1>(machine.transitions[j]) = index[k];
						}
						cout << std::get<0>(machine.transitions[j]) << "   " << std::get<1>(machine.transitions[j]) << "    " << std::get<2>(machine.transitions[j]);
						cout << endl;
					}
				}
			}
		}
	}
}
int main()
{
	ifstream file("Text.txt");
	works::Isomorphism::start(file);
	cout << endl;
	cout << endl;
	works::equivalence::start(file);
	cout << endl;
	cout << endl;
	//works::Minimization::start(file);
	works::Hopcroft::start(file);
	return 0;
}