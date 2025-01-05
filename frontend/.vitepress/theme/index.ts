// https://vitepress.dev/guide/custom-theme
import { h } from 'vue'
import type { Theme } from 'vitepress'
import DefaultTheme from 'vitepress/theme'
import './style.css'
import 'primeicons/primeicons.css';
import PrimeVue from 'primevue/config';
import Button from "primevue/button";
import AutoComplete from "primevue/autocomplete";
import SelectButton from 'primevue/selectbutton';
import { definePreset } from '@primevue/themes';
import Aura from '@primevue/themes/aura';

const MyPreset = definePreset(Aura, {
  semantic: {
    primary: {
      50: '{blue.50}',
      100: '{blue.100}',
      200: '{blue.200}',
      300: '{blue.300}',
      400: '{blue.400}',
      500: '{blue.500}',
      600: '{blue.600}',
      700: '{blue.700}',
      800: '{blue.800}',
      900: '{blue.900}',
      950: '{blue.950}'
    }
  }
});


export default {
  extends: DefaultTheme,
  Layout: () => {
    return h(DefaultTheme.Layout, null, {
      // https://vitepress.dev/guide/extending-default-theme#layout-slots
    })
  },
  enhanceApp({ app, router, siteData }) {
    app.use(PrimeVue, {
      theme: {
        preset: MyPreset,
        options: {
          prefix: 'p',
          darkModeSelector: 'system',
          cssLayer: false
        }
      }
    });
    app.component('Button', Button);
    app.component('AutoComplete', AutoComplete);
    app.component('SelectButton', SelectButton);
  }
} satisfies Theme
