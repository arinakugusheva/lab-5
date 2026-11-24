"""
Лабораторная работа № 5. Вариант 13.
Кугушева Арина, группа БИ2-1.
Дисциплина: Теория алгоритмов.

ХЕШИРОВАНИЕ И ИССЛЕДОВАНИЕ МЕТОДОВ РАЗРЕШЕНИЯ КОЛЛИЗИЙ

Условия варианта 13:
    * тип ключей ............ целые числа, кратные 100 (100, 200, 300, ...);
    * хеш-функция ........... метод деления:  h(k) = k mod m;
    * разрешение коллизий ... метод цепочек (Ц) и двойное хеширование (Дв);
    * число элементов n ..... 30 000;
    * размер таблицы m ...... 49 999 (простое число);
    * дополнительное В6 .... кластеризация при линейном пробировании:
                              распределение длин непрерывных занятых
                              участков при разных коэффициентах заполнения.

КАК УСТРОЕН ФАЙЛ (читать сверху вниз)
    Часть 1. Константы и генерация ключей.
    Часть 2. Хеш-функции.
    Часть 3. Таблица с цепочками            (класс ChainHashTable).
    Часть 4. Таблица с открытой адресацией  (класс OpenHashTable;
             режим "double" — двойное хеширование, режим "linear" — линейное
             пробирование, оно нужно для задания В6).
    Часть 5. Вспомогательные функции измерения.
    Часть 6. Эксперименты (каждый — отдельная функция experiment_*).
    Часть 7. Проверка правильности (самотесты) и вывод.
    Часть 8. Графики и точка входа main().

ЗАПУСК
    python lab5_variant13.py                       # все эксперименты
    python lab5_variant13.py --plots plots         # + графики в папку plots
    python lab5_variant13.py --json results.json   # + результаты в файл JSON
"""

import argparse   # разбор параметров командной строки (--plots, --json)
import json       # запись результатов в файл
import math       # логарифм и экспонента для теоретических формул
import random     # генерация случайных ключей
import statistics  # медиана для устойчивых замеров времени
import time       # измерение времени работы


# =====================================================================
# ЧАСТЬ 1. КОНСТАНТЫ И ГЕНЕРАЦИЯ КЛЮЧЕЙ
# =====================================================================

N = 30_000          # сколько ключей кладём в таблицу (по варианту)
M = 49_999          # размер таблицы (по варианту, простое число)
KEY_STEP = 100      # ключи кратны 100
SEED = 42           # зерно генератора: при каждом запуске числа одинаковые
QUERIES = 10_000    # сколько запросов поиска делаем при измерениях
REPEATS = 3         # сколько раз повторяем замер времени (берём медиану)

# Коэффициенты заполнения для графика «число проб — alpha»
ALPHAS = [0.1, 0.3, 0.5, 0.7, 0.9, 0.95]
# Коэффициенты заполнения для исследования кластеризации (задание В6)
CLUSTER_ALPHAS = [0.3, 0.5, 0.7, 0.9, 0.95]


def make_keys(count, rng):
    """Возвращает список из count РАЗНЫХ случайных чисел, кратных 100.

    Как это работает:
      1) rng.sample(range(1, 1_000_000), count) выбирает count различных
         номеров j из диапазона 1…999 999 (без повторов);
      2) каждый номер умножаем на 100 — получаем ключ k = 100·j.
    Поэтому все ключи кратны 100, а повторов среди них нет.
    """
    numbers = rng.sample(range(1, 1_000_000), count)
    return [KEY_STEP * j for j in numbers]


# =====================================================================
# ЧАСТЬ 2. ХЕШ-ФУНКЦИИ
# =====================================================================
# Хеш-функция превращает ключ (большое число) в номер ячейки таблицы
# от 0 до m − 1. Разные ключи могут дать один номер — это КОЛЛИЗИЯ.

def hash_division(key, m):
    """Основная хеш-функция варианта — метод деления: h(k) = k mod m.

    Почему m берут ПРОСТЫМ (49 999 — простое число)?
    Наши ключи кратны 100 = 2·2·5·5. Если бы m имело общие делители
    со 100 (например, m = 50 000), то остатки k mod m принимали бы лишь
    малую долю значений, и ключи сбились бы в немногих ячейках.
    У простого m общих делителей со 100 нет — остатки рассыпаются по
    всей таблице. Это показано в эксперименте experiment_hash_quality.
    """
    return key % m


def hash_step(key, m):
    """Второй хеш для двойного хеширования: h2(k) = 1 + (k mod (m − 1)).

    Это ШАГ, с которым мы перепрыгиваем по таблице при коллизии.
    Требования к шагу:
      * он не должен быть нулём — иначе мы стояли бы на месте
        (поэтому прибавляем 1: шаг от 1 до m − 1);
      * он должен быть взаимно прост с m — тогда проба обойдёт ВСЕ ячейки.
        Так как m = 49 999 простое, любой шаг от 1 до m − 1 подходит.
    """
    return 1 + key % (m - 1)


def hash_bad(key, m):
    """Заведомо плохая хеш-функция h(k) = k mod 10 (отрицательный пример).

    Она даёт только 10 разных значений, а у НАШИХ ключей (кратных 100)
    всегда одно значение — 0: все ключи попадают в одну ячейку!
    Параметр m не используется, он нужен лишь для единого вида вызова.
    """
    return key % 10


# =====================================================================
# ЧАСТЬ 3. ХЕШ-ТАБЛИЦА С МЕТОДОМ ЦЕПОЧЕК
# =====================================================================

class ChainHashTable:
    """Таблица, где каждая ячейка хранит СПИСОК пар (ключ, значение).

    Если два ключа попали в одну ячейку, они просто лежат в одном списке
    («цепочке»). Схема:
        ячейка 0 -> [(k1, v1), (k7, v7)]
        ячейка 1 -> []
        ячейка 2 -> [(k4, v4)]   и т. д.

    «Проба» в этой таблице — одно сравнение ключа с элементом цепочки.
    Счётчик self.probes накапливает число проб, чтобы потом считать среднее.
    """

    def __init__(self, m=M, hash_func=hash_division):
        self.m = m                                # число ячеек
        self.hash_func = hash_func                # используемая хеш-функция
        self.slots = [[] for _ in range(m)]       # m пустых цепочек
        self.n = 0                                # сколько элементов хранится
        self.probes = 0                           # счётчик проб

    def insert(self, key, value):
        """Добавляет пару (key, value); если ключ уже есть — меняет значение."""
        chain = self.slots[self.hash_func(key, self.m)]   # нужная цепочка
        for i in range(len(chain)):               # ищем ключ в цепочке
            self.probes += 1                      # одно сравнение = одна проба
            if chain[i][0] == key:                # ключ уже есть
                chain[i] = (key, value)           # обновляем значение
                return
        chain.append((key, value))                # ключа не было — добавляем
        self.n += 1

    def search(self, key):
        """Возвращает значение по ключу или None, если ключа нет."""
        chain = self.slots[self.hash_func(key, self.m)]
        for stored_key, value in chain:           # перебираем цепочку
            self.probes += 1
            if stored_key == key:
                return value
        return None                               # дошли до конца — ключа нет

    def delete(self, key):
        """Удаляет ключ. Возвращает True, если удалили, иначе False.

        В цепочках удаление простое: достаём элемент из списка.
        """
        chain = self.slots[self.hash_func(key, self.m)]
        for i in range(len(chain)):
            self.probes += 1
            if chain[i][0] == key:
                del chain[i]
                self.n -= 1
                return True
        return False

    def chain_lengths(self):
        """Длины всех цепочек (по одной на ячейку) — для гистограммы."""
        return [len(chain) for chain in self.slots]


# =====================================================================
# ЧАСТЬ 4. ХЕШ-ТАБЛИЦА С ОТКРЫТОЙ АДРЕСАЦИЕЙ
# =====================================================================

class OpenHashTable:
    """Таблица, где все элементы лежат прямо в массиве (без списков).

    Если нужная ячейка занята, мы ПРОБИРУЕМ другие ячейки по правилу.
    Номер i-й пробы:
        режим "double" (двойное хеширование): pos = (h1 + i·h2) mod m
        режим "linear" (линейное пробирование): pos = (h1 + i)   mod m
    где h1 = k mod m — начальная ячейка, h2 — шаг (см. hash_step).
    Линейное пробирование — это то же самое с шагом, всегда равным 1.

    Три состояния ячейки хранятся в массиве self.keys:
        EMPTY   — ячейка никогда не использовалась;
        DELETED — ячейка использовалась, но элемент удалён («надгробие»);
        иначе   — в ячейке лежит ключ.

    Зачем нужна пометка DELETED? Поиск останавливается на первой EMPTY
    ячейке («дальше искать нечего»). Если при удалении просто сделать
    ячейку EMPTY, цепочка проб разорвётся, и элементы, лежавшие ПОСЛЕ неё,
    станут «невидимыми». Пометка DELETED говорит: «иди дальше».

    «Проба» здесь — один просмотр ячейки массива.
    """

    EMPTY = object()      # уникальные «метки»: сравниваем их через is
    DELETED = object()

    def __init__(self, m=M, mode="double"):
        if mode not in ("double", "linear"):
            raise ValueError("mode должен быть 'double' или 'linear'")
        self.m = m
        self.mode = mode
        self.keys = [self.EMPTY] * m              # ключи (или метки)
        self.values = [None] * m                  # значения
        self.n = 0                                # число хранимых элементов
        self.probes = 0

    def _first_cell_and_step(self, key):
        """Возвращает (начальная ячейка, шаг) для данного ключа."""
        first = hash_division(key, self.m)
        step = 1 if self.mode == "linear" else hash_step(key, self.m)
        return first, step

    def insert(self, key, value):
        """Кладёт пару (key, value). Если ключ уже есть — обновляет значение."""
        if self.n >= self.m:                      # места нет вообще
            raise RuntimeError("Таблица переполнена")
        pos, step = self._first_cell_and_step(key)
        first_free = -1                           # первая встретившаяся свободная
        for _ in range(self.m):                   # не более m проб
            self.probes += 1
            current = self.keys[pos]
            if current is self.EMPTY:             # дошли до конца цепочки проб
                if first_free == -1:
                    first_free = pos
                break                             # ключа в таблице точно нет
            if current is self.DELETED:           # «надгробие»: запоминаем место,
                if first_free == -1:              # но ищем дальше — вдруг ключ
                    first_free = pos              # лежит ниже
            elif current == key:                  # ключ уже есть
                self.values[pos] = value          # обновляем значение
                return
            pos = (pos + step) % self.m           # следующая проба
        if first_free == -1:                      # свободной ячейки не нашли
            raise RuntimeError("Таблица переполнена")
        self.keys[first_free] = key
        self.values[first_free] = value
        self.n += 1

    def search(self, key):
        """Возвращает значение по ключу или None."""
        pos, step = self._first_cell_and_step(key)
        for _ in range(self.m):
            self.probes += 1
            current = self.keys[pos]
            if current is self.EMPTY:             # пустая ячейка: ключа нет
                return None
            if current is not self.DELETED and current == key:
                return self.values[pos]
            pos = (pos + step) % self.m           # иначе идём дальше
        return None

    def delete(self, key, mark_deleted=True):
        """Удаляет ключ. Возвращает True, если удалили.

        mark_deleted=True  — правильно: ставим метку DELETED.
        mark_deleted=False — НЕПРАВИЛЬНО (ячейка становится EMPTY); нужно
        только для демонстрации, что так удалять нельзя.
        """
        pos, step = self._first_cell_and_step(key)
        for _ in range(self.m):
            self.probes += 1
            current = self.keys[pos]
            if current is self.EMPTY:
                return False
            if current is not self.DELETED and current == key:
                self.keys[pos] = self.DELETED if mark_deleted else self.EMPTY
                self.values[pos] = None
                self.n -= 1
                return True
            pos = (pos + step) % self.m
        return False

    def cluster_lengths(self):
        """Длины непрерывных занятых участков («кластеров») — задание В6.

        Идём по массиву слева направо и считаем подряд идущие занятые ячейки.
        Ячейка занята, если в ней не метка EMPTY (метка DELETED тоже
        считается занятой: на ней проба не останавливается).
        Массив считаем линейным (без «склейки» конца с началом).
        """
        lengths = []
        current_run = 0
        for key in self.keys:
            if key is not self.EMPTY:             # ячейка занята
                current_run += 1                  # участок продолжается
            elif current_run > 0:                 # участок закончился
                lengths.append(current_run)
                current_run = 0
        if current_run > 0:                       # участок дошёл до конца массива
            lengths.append(current_run)
        return lengths


# =====================================================================
# ЧАСТЬ 5. ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ИЗМЕРЕНИЯ
# =====================================================================

def timed(function, repeats=REPEATS):
    """Запускает function() несколько раз и возвращает МЕДИАНУ времени.

    Медиана (а не среднее) нужна, чтобы единичный случайный «скачок»
    времени из-за фоновых процессов не исказил результат.
    Каждый вызов function() должен сам готовить всё необходимое (например,
    создавать новую пустую таблицу), чтобы запуски были независимы.
    Возвращает (время в секундах, результат последнего запуска).
    """
    times = []
    result = None
    for _ in range(repeats):
        start = time.perf_counter()
        result = function()
        times.append(time.perf_counter() - start)
    return statistics.median(times), result


def fill(table, keys):
    """Вставляет все ключи в таблицу (значением служит сам ключ)."""
    for key in keys:
        table.insert(key, key)
    return table


def average_probes(table, queries):
    """Среднее число проб на один поиск по списку запросов."""
    table.probes = 0                              # обнуляем счётчик
    for q in queries:
        table.search(q)
    return table.probes / len(queries)


def absent_keys(keys, count, rng):
    """Ключи, которых в таблице НЕТ (но того же вида — кратные 100).

    Нужны для «неуспешного поиска». Берём случайные кратные 100 и
    отбрасываем те, что случайно оказались в таблице.
    """
    present = set(keys)
    result = []
    while len(result) < count:
        candidate = KEY_STEP * rng.randrange(1, 1_000_000)
        if candidate not in present:
            result.append(candidate)
    return result


# --- теоретические формулы для сравнения с экспериментом --------------
def theory_chain_success(alpha):
    """Цепочки, успешный поиск: в среднем 1 + alpha/2 сравнений."""
    return 1 + alpha / 2


def theory_chain_fail(alpha):
    """Цепочки, неуспешный поиск: просматривается вся цепочка, то есть alpha."""
    return alpha


def theory_double_success(alpha):
    """Двойное хеширование, успешный поиск: (1/alpha)·ln(1/(1 − alpha))."""
    return math.log(1 / (1 - alpha)) / alpha


def theory_double_fail(alpha):
    """Двойное хеширование, неуспешный поиск: 1/(1 − alpha) (формула из методички)."""
    return 1 / (1 - alpha)


def theory_linear_success(alpha):
    """Линейное пробирование, успешный поиск: (1 + 1/(1 − alpha)) / 2."""
    return 0.5 * (1 + 1 / (1 - alpha))


def theory_linear_fail(alpha):
    """Линейное пробирование, неуспешный поиск: (1 + 1/(1 − alpha)²) / 2."""
    return 0.5 * (1 + 1 / (1 - alpha) ** 2)


# =====================================================================
# ЧАСТЬ 6. ЭКСПЕРИМЕНТЫ
# =====================================================================

def experiment_main():
    """Основной эксперимент варианта: n = 30 000, m = 49 999.

    Сравниваем: цепочки, двойное хеширование и встроенный dict (эталон).
    Для каждого измеряем время вставки, время поиска и среднее число проб.
    """
    rng = random.Random(SEED)
    keys = make_keys(N, rng)                              # что вставляем
    hits = [rng.choice(keys) for _ in range(QUERIES)]     # успешные запросы
    misses = absent_keys(keys, QUERIES, rng)              # неуспешные запросы
    alpha = N / M
    result = {"n": N, "m": M, "alpha": alpha, "tables": {}}

    # Описываем, как создавать каждую таблицу
    builders = {
        "chain": lambda: ChainHashTable(),
        "double": lambda: OpenHashTable(mode="double"),
    }
    for name, build in builders.items():
        # --- время вставки (каждый раз новая пустая таблица) ---
        t_insert, table = timed(lambda: fill(build(), keys))
        # --- время поиска существующих ключей ---
        t_search, _ = timed(lambda: [table.search(q) for q in hits])
        # --- среднее число проб ---
        probes_hit = average_probes(table, hits)
        probes_miss = average_probes(table, misses)
        result["tables"][name] = {
            "t_insert": t_insert, "t_search": t_search,
            "probes_hit": probes_hit, "probes_miss": probes_miss,
        }
        if name == "chain":
            lengths = table.chain_lengths()
            result["chains"] = {
                "max": max(lengths),
                "empty": lengths.count(0),
                "mean": sum(lengths) / len(lengths),
                "histogram": {str(L): lengths.count(L) for L in range(max(lengths) + 1)},
            }

    # --- встроенный dict как эталон ---
    t_insert, d = timed(lambda: {k: k for k in keys})
    t_search, _ = timed(lambda: [d.get(q) for q in hits])
    result["tables"]["dict"] = {"t_insert": t_insert, "t_search": t_search}

    # --- сколько различных значений принимает шаг h2 (проверка второго хеша) ---
    steps = {hash_step(k, M) for k in keys}
    result["distinct_steps"] = len(steps)
    result["distinct_h1"] = len({hash_division(k, M) for k in keys})
    return result


def experiment_alpha():
    """Зависимость числа проб от коэффициента заполнения alpha.

    Для каждого alpha из ALPHAS строим таблицы размера M с n = alpha·M
    ключами и измеряем среднее число проб при успешном и неуспешном поиске.
    Исследуем три способа: цепочки, двойное хеширование, линейное
    пробирование (последнее — как «плохой» пример для сравнения).
    """
    rng = random.Random(SEED + 1)
    rows = []
    for alpha in ALPHAS:
        n = round(alpha * M)
        keys = make_keys(n, rng)
        hits = [rng.choice(keys) for _ in range(QUERIES)]
        misses = absent_keys(keys, QUERIES, rng)
        row = {"alpha": alpha, "n": n}
        tables = {
            "chain": fill(ChainHashTable(), keys),
            "double": fill(OpenHashTable(mode="double"), keys),
            "linear": fill(OpenHashTable(mode="linear"), keys),
        }
        for name, table in tables.items():
            row[name + "_hit"] = average_probes(table, hits)
            row[name + "_miss"] = average_probes(table, misses)
        # теоретические значения
        row["theory"] = {
            "chain_hit": theory_chain_success(alpha), "chain_miss": theory_chain_fail(alpha),
            "double_hit": theory_double_success(alpha), "double_miss": theory_double_fail(alpha),
            "linear_hit": theory_linear_success(alpha), "linear_miss": theory_linear_fail(alpha),
        }
        rows.append(row)
    return rows


# Границы интервалов длин кластеров для таблицы (нижняя, верхняя, подпись)
CLUSTER_BINS = [(1, 1, "1"), (2, 2, "2"), (3, 4, "3–4"), (5, 8, "5–8"), (9, 16, "9–16"),
                (17, 32, "17–32"), (33, 64, "33–64"), (65, 10 ** 9, "65 и более")]


def cluster_histogram(lengths):
    """Раскладывает длины кластеров по интервалам CLUSTER_BINS."""
    counts = []
    for low, high, _ in CLUSTER_BINS:
        counts.append(sum(1 for length in lengths if low <= length <= high))
    return counts


def experiment_clusters():
    """Задание В6: кластеризация при линейном пробировании.

    Для каждого alpha вставляем alpha·M ключей в таблицу с линейным
    пробированием и смотрим длины непрерывных занятых участков. Для
    сравнения делаем то же с двойным хешированием и теми же ключами.
    Ожидание: при линейном пробировании кластеры длиннее («первичная
    кластеризация»), а при двойном — короче.
    """
    rng = random.Random(SEED + 2)
    rows = []
    for alpha in CLUSTER_ALPHAS:
        n = round(alpha * M)
        keys = make_keys(n, rng)
        row = {"alpha": alpha, "n": n}
        for mode in ("linear", "double"):
            table = fill(OpenHashTable(mode=mode), keys)
            lengths = table.cluster_lengths()
            row[mode] = {
                "clusters": len(lengths),                       # сколько участков
                "mean": sum(lengths) / len(lengths),            # средняя длина
                "max": max(lengths),                            # самый длинный
                "histogram": cluster_histogram(lengths),        # по интервалам
                "free_cells": M - n,
            }
        rows.append(row)
    return rows


def experiment_hash_quality(n=3000):
    """Сравнение хороших и плохих хеш-функций (для защиты и выводов).

    Берём n = 3000 ключей (для плохой функции все ключи попадут в одну
    цепочку, и при 30 000 ключей вставка заняла бы минуты) и сравниваем
    метод цепочек для трёх вариантов:
      1) h(k) = k mod 49 999 — основная функция (m простое);
      2) h(k) = k mod 50 000 — m не простое и имеет общие делители со 100;
      3) h(k) = k mod 10     — заведомо плохая функция из методички.
    """
    rng = random.Random(SEED + 3)
    keys = make_keys(n, rng)
    queries = [rng.choice(keys) for _ in range(1000)]
    variants = [
        ("k mod 49 999 (m простое)", hash_division, 49_999),
        ("k mod 50 000 (m не простое)", hash_division, 50_000),
        ("k mod 10 (плохая)", hash_bad, 49_999),
    ]
    rows = []
    for label, func, m in variants:
        table = fill(ChainHashTable(m, func), keys)
        lengths = table.chain_lengths()
        rows.append({
            "label": label, "m": m,
            "used_cells": m - lengths.count(0),               # непустых ячеек
            "max_chain": max(lengths),                        # самая длинная цепочка
            "probes": average_probes(table, queries),         # проб на запрос
        })
    return {"n": n, "rows": rows}


def experiment_delete():
    """Демонстрация: простое обнуление ячейки ломает поиск (пометка DELETED — нет).

    Строим маленькую таблицу, где три ключа образуют цепочку проб:
    первый лежит в «своей» ячейке, второй и третий — после него.
    Удаляем первый двумя способами и ищем третий.
    """
    results = {}
    for label, mark in (("с пометкой DELETED", True), ("простым обнулением", False)):
        table = OpenHashTable(m=11, mode="linear")
        # 100 mod 11 = 1; 1100 mod 11 = 0 ... подберём три ключа с одной стартовой ячейкой
        keys = [100, 100 + 11 * 100, 100 + 22 * 100]       # все дают h = 1 (mod 11)
        for k in keys:
            table.insert(k, k)
        table.delete(keys[0], mark_deleted=mark)
        results[label] = {
            "third_found": table.search(keys[2]) is not None,
            "start_cell": hash_division(keys[0], 11),
            "keys": keys,
        }
    return results


# =====================================================================
# ЧАСТЬ 7. ПРОВЕРКА ПРАВИЛЬНОСТИ
# =====================================================================

def check_correctness():
    """Самотесты: обе таблицы ведут себя как обычный dict.

    Выполняем одну и ту же случайную последовательность операций
    (вставка / поиск / удаление) над нашей таблицей и над dict. Если хоть
    раз результаты различаются — assert остановит программу с ошибкой.
    """
    rng = random.Random(7)
    for table_class_args in (("chain",), ("double",), ("linear",)):
        kind = table_class_args[0]
        # маленькая таблица (простое m = 101), чтобы коллизий было много
        table = ChainHashTable(101) if kind == "chain" else OpenHashTable(101, kind)
        reference = {}                                       # эталон
        for _ in range(3000):
            key = 100 * rng.randrange(1, 60)                 # мало разных ключей
            action = rng.choice(["insert", "search", "delete"])
            if action == "insert" and (kind == "chain" or len(reference) < 60):
                table.insert(key, key + 1)
                reference[key] = key + 1
            elif action == "search":
                assert table.search(key) == reference.get(key)
            else:
                removed = table.delete(key)
                assert removed == (key in reference)
                reference.pop(key, None)
        # в конце всё содержимое должно совпасть
        for key in range(100, 6000, 100):
            assert table.search(key) == reference.get(key)
    # шаг двойного хеширования всегда в диапазоне 1..m-1
    for k in range(100, 100_000, 100):
        assert 1 <= hash_step(k, M) <= M - 1
    return True


# =====================================================================
# ЧАСТЬ 8. ВЫВОД, ГРАФИКИ, ТОЧКА ВХОДА
# =====================================================================

def f(x, digits=3):
    """Число в строку с десятичной ЗАПЯТОЙ (так принято в отчётах)."""
    return f"{x:.{digits}f}".replace(".", ",")


def print_report(res):
    main = res["main"]
    print("=" * 74)
    print(f"Таблица 1. n = {main['n']}, m = {main['m']}, alpha = {f(main['alpha'])}")
    print(f"{'Реализация':<24}{'вставка, с':>12}{'поиск, с':>11}{'проб (есть)':>13}{'проб (нет)':>12}")
    for name, label in (("chain", "Метод цепочек"), ("double", "Двойное хеширование"), ("dict", "dict (эталон)")):
        t = main["tables"][name]
        pr_hit = f(t["probes_hit"], 2) if "probes_hit" in t else "—"
        pr_miss = f(t["probes_miss"], 2) if "probes_miss" in t else "—"
        print(f"{label:<24}{f(t['t_insert']):>12}{f(t['t_search'], 4):>11}{pr_hit:>13}{pr_miss:>12}")
    ch = main["chains"]
    print(f"\nЦепочки: средняя длина {f(ch['mean'], 2)}, максимальная {ch['max']}, "
          f"пустых ячеек {ch['empty']} из {main['m']} ({f(ch['empty'] / main['m'] * 100, 1)} %)")
    print(f"Различных значений h1 среди ключей: {main['distinct_h1']}, различных шагов h2: {main['distinct_steps']}")

    print("\nТаблица 2. Среднее число проб (эксперимент / теория)")
    print(f"{'alpha':>6}{'цеп. есть':>14}{'цеп. нет':>14}{'дв. есть':>14}{'дв. нет':>14}{'лин. есть':>14}{'лин. нет':>14}")
    for r in res["alpha"]:
        th = r["theory"]
        cells = [f"{f(r[k], 2)}/{f(th[k], 2)}" for k in ("chain_hit", "chain_miss", "double_hit", "double_miss", "linear_hit", "linear_miss")]
        print(f"{r['alpha']:>6}" + "".join(f"{c:>14}" for c in cells))

    print("\nВ6. Кластеры (линейное пробирование / двойное хеширование)")
    print(f"{'alpha':>6}{'кластеров (л/дв)':>22}{'средняя длина':>18}{'максимум':>14}")
    for r in res["clusters"]:
        l, d = r["linear"], r["double"]
        print(f"{r['alpha']:>6}{str(l['clusters']) + '/' + str(d['clusters']):>22}"
              f"{f(l['mean'], 2) + '/' + f(d['mean'], 2):>18}{str(l['max']) + '/' + str(d['max']):>14}")

    print("\nКачество хеш-функции (метод цепочек, n = %d)" % res["quality"]["n"])
    for r in res["quality"]["rows"]:
        print(f"  {r['label']:<30} занято ячеек {r['used_cells']:>6}, макс. цепочка {r['max_chain']:>5}, проб на запрос {f(r['probes'], 2)}")

    print("\nУдаление (проверка, находится ли третий ключ цепочки после удаления первого)")
    for label, r in res["delete"].items():
        print(f"  {label:<22} -> {'найден' if r['third_found'] else 'НЕ найден'}")


def save_plots(res, directory):
    """Строит графики (нужен пакет matplotlib)."""
    import os
    import matplotlib
    matplotlib.use("Agg")                     # режим без окна: просто сохраняем файлы
    import matplotlib.pyplot as plt
    os.makedirs(directory, exist_ok=True)

    # --- график 1: число проб и теоретические кривые ---
    rows = res["alpha"]
    xs = [r["alpha"] for r in rows]
    fine = [i / 200 for i in range(10, 196)]                  # гладкая кривая
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.2))
    for ax, suffix, title, formulas in (
            (axes[0], "hit", "Успешный поиск", {"chain": theory_chain_success, "double": theory_double_success, "linear": theory_linear_success}),
            (axes[1], "miss", "Неуспешный поиск", {"chain": theory_chain_fail, "double": theory_double_fail, "linear": theory_linear_fail})):
        for name, label, color in (("chain", "цепочки", "#1f77b4"), ("double", "двойное хеширование", "#2ca02c"), ("linear", "линейное пробирование", "#d62728")):
            ax.plot(xs, [r[f"{name}_{suffix}"] for r in rows], "o", color=color, label=label + " (опыт)")
            ax.plot(fine, [formulas[name](a) for a in fine], "-", color=color, lw=1, alpha=.7)
        ax.set_yscale("log")
        ax.set_xlabel("коэффициент заполнения α")
        ax.set_ylabel("среднее число проб (лог. шкала)")
        ax.set_title(title + ": точки — опыт, линии — теория")
        ax.grid(alpha=.3, which="both")
    axes[0].legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(os.path.join(directory, "probes_alpha.png"), dpi=200)
    plt.close(fig)

    # --- график 2: распределение длин кластеров (В6) ---
    rows = res["clusters"]
    labels = [b[2] for b in CLUSTER_BINS]
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.2), sharey=True)
    width = 0.8 / len(rows)
    for ax, mode, title in ((axes[0], "linear", "Линейное пробирование"), (axes[1], "double", "Двойное хеширование")):
        for i, r in enumerate(rows):
            ax.bar([x + i * width for x in range(len(labels))], [c if c > 0 else float("nan") for c in r[mode]["histogram"]],
                   width, label=f"α = {r['alpha']}".replace(".", ","))
        ax.set_xticks([x + 0.4 - width / 2 for x in range(len(labels))])
        ax.set_xticklabels(labels, rotation=30)
        ax.set_yscale("log")
        ax.set_xlabel("длина непрерывного занятого участка")
        ax.set_title(title)
        ax.grid(alpha=.3, axis="y")
    axes[0].set_ylabel("число участков (лог. шкала)")
    axes[0].legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(os.path.join(directory, "clusters.png"), dpi=200)
    plt.close(fig)

    # --- график 3: длины цепочек ---
    hist = res["main"]["chains"]["histogram"]
    fig, ax = plt.subplots(figsize=(6, 3.8))
    lens = sorted(int(k) for k in hist)
    ax.bar(lens, [hist[str(L)] for L in lens], color="#1f77b4")
    alpha = res["main"]["alpha"]
    ax.plot(lens, [M * math.exp(-alpha) * alpha ** L / math.factorial(L) for L in lens], "ro-", label="распределение Пуассона")
    ax.set_xlabel("длина цепочки")
    ax.set_ylabel("число ячеек")
    ax.set_title("Длины цепочек, n = 30 000, m = 49 999")
    ax.legend()
    ax.grid(alpha=.3, axis="y")
    fig.tight_layout()
    fig.savefig(os.path.join(directory, "chains.png"), dpi=200)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--plots", metavar="DIR", help="папка для графиков")
    parser.add_argument("--json", metavar="FILE", help="файл для результатов JSON")
    args = parser.parse_args()

    check_correctness()                                       # 1) самотесты
    print("Самотесты пройдены: обе таблицы ведут себя как dict")
    results = {                                               # 2) эксперименты
        "main": experiment_main(),
        "alpha": experiment_alpha(),
        "clusters": experiment_clusters(),
        "quality": experiment_hash_quality(),
        "delete": experiment_delete(),
    }
    print_report(results)                                     # 3) вывод в консоль
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(results, fh, ensure_ascii=False, indent=1)
    if args.plots:
        save_plots(results, args.plots)


if __name__ == "__main__":
    main()
