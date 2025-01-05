---
outline: page
---

<script setup>
import CodeMirror from 'vue-codemirror6';
import {ayuLight, dracula} from 'thememirror';

import { onMounted, ref } from 'vue';

const algorithms = ref(null);
const selectedAlgorithm = ref(null);
const autoFilteredAlg = ref([]);

const selectButtonValue = ref({ name: 'Paper' });
const selectButtonValues = ref([{ name: 'Paper' }, { name: 'Extended' }]);

const examples = ref(null);
const selectedExample = ref(null);
const autoFilteredEx = ref([]);

const code = ref('');
const loading = ref(false);

const themeExt = ref([ayuLight]);

function load() {
    loading.value = true;
    setTimeout(() => (loading.value = false), 200);
}

onMounted(() => {
    algorithms.value = [
        { name: 'Algorithm W', code: 'W' },
        { name: 'Elementary Type Inference', code: 'Elementary' },
    ];
    examples.value = [
        { name: '(\\x. x) 1', code: '(\\x. x) 1' },
        { name: 'let id = \\x. x in (id 1, id True)', code: 'let id = \\x. x in (id 1, id True)' },
    ];
});

function searchAlgorithm(event) {
    if (!event.query.trim().length) {
        autoFilteredAlg.value = [...algorithms.value];
    } else {
        autoFilteredAlg.value = algorithms.value.filter((alg) => {
            return alg.name.toLowerCase().startsWith(event.query.toLowerCase());
        });
    };
}

function searchExample(event) {
    if (!event.query.trim().length) {
        autoFilteredEx.value = [...examples.value];
    } else {
        autoFilteredEx.value = examples.value.filter((ex) => {
            return ex.name.toLowerCase().startsWith(event.query.toLowerCase());
        });
    };
}

function handleExampleSelect(event) {
  const selected = event.value;
  if (selected && selected.code) {
    code.value = selected.code;
  }
}

const updateCodeMirrorTheme = () => {
  if (document.documentElement.classList.contains('dark')) {
    themeExt.value = [dracula];
  } else {
    themeExt.value = [ayuLight];
  }
};

onMounted(() => {
  updateCodeMirrorTheme();
  const observer = new MutationObserver(() => {
    updateCodeMirrorTheme();
  });
  observer.observe(document.documentElement, { attributes: true, attributeFilter: ['class'] });
});
</script>


<div class="flex flex-wrap items-start gap-4 mb-4">
    <AutoComplete v-model="selectedAlgorithm" :suggestions="autoFilteredAlg" optionLabel="name"
        placeholder="Select Algorithm" dropdown display="chip" @complete="searchAlgorithm($event)" />
    <SelectButton v-model="selectButtonValue" :options="selectButtonValues" optionLabel="name" />
</div>

<div class="flex flex-wrap items-start gap-4 mb-4">
    <AutoComplete v-model="selectedExample" :suggestions="autoFilteredEx" optionLabel="name"
        placeholder="Load Example Program" dropdown display="chip" @complete="searchExample($event)"
        @option-select="handleExampleSelect" />
    <Button type="button" label="Infer" icon="pi pi-caret-right" :loading="loading" @click="load" />
</div>

<div class="mt-2 mb-2">
    <code-mirror v-model="code" :extensions="themeExt" basic></code-mirror>
</div>
